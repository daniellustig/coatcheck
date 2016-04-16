(******************************************************************************)
(* PipeCheck: Specifying and Verifying Microarchitectural                     *)
(* Enforcement of Memory Consistency Models                                   *)
(*                                                                            *)
(* Copyright (c) 2015 Daniel Lustig, Princeton University                     *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* This library is free software; you can redistribute it and/or              *)
(* modify it under the terms of the GNU Lesser General Public                 *)
(* License as published by the Free Software Foundation; either               *)
(* version 2.1 of the License, or (at your option) any later version.         *)
(*                                                                            *)
(* This library is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU          *)
(* Lesser General Public License for more details.                            *)
(*                                                                            *)
(* You should have received a copy of the GNU Lesser General Public           *)
(* License along with this library; if not, write to the Free Software        *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  *)
(* USA                                                                        *)
(******************************************************************************)

open Str
open Map
open PipeGraph

let rec pipegraphStringHelper s n l =
  try
    pipegraphStringHelper s (n+1) (String.get s n :: l)
  with Invalid_argument _ ->
    List.rev_append l []

let pipegraphString s = pipegraphStringHelper s 0 []

module AddressMap = Map.Make(String)
module DataMap = Map.Make(String)

let addressMap = ref AddressMap.empty
let _ = addressMap := AddressMap.add "x" 0 !addressMap
let _ = addressMap := AddressMap.add "y" 1 !addressMap
let _ = addressMap := AddressMap.add "z" 2 !addressMap
let _ = addressMap := AddressMap.add "w" 3 !addressMap

let dataMap  = ref DataMap.empty
let _ = dataMap := DataMap.add "0" 0 !dataMap
let _ = dataMap := DataMap.add "1" 1 !dataMap
let _ = dataMap := DataMap.add "2" 2 !dataMap
let _ = dataMap := DataMap.add "3" 3 !dataMap

let rec appendToNth l n a =
  match (l, n) with
  | (h::t, 0) -> (h @ [a])::t
  | (h::t, _) -> h :: appendToNth t (n-1) a
  | ([], 0) -> [[a]]
  | ([], _) -> [] :: appendToNth [] (n-1) a

module IntMap = Map.Make(struct type t = int let compare = compare end)

let rec renumber_edges eiids edges =
  match edges with
  | (PipeGraph.Pair (PipeGraph.Pair (h1, h2), hl))::t ->
      let h1' = IntMap.find h1 eiids in
      let h2' = IntMap.find h2 eiids in
      let h' = PipeGraph.Pair (PipeGraph.Pair (h1', h2'), hl) in
      h' :: renumber_edges eiids t
  | [] -> []

let rec renumber_accesses_helper result ops edges eiids next_eiid =
  match ops with
  | h::t ->
      let old_eiid = globalID h in
      let already_exists = IntMap.mem old_eiid eiids in
      let new_eiid = if already_exists then IntMap.find old_eiid eiids
        else next_eiid in
      let next_eiid' = if already_exists then next_eiid else next_eiid + 1 in
      let eiids' = if already_exists then eiids
        else IntMap.add old_eiid new_eiid eiids in
      let h' = {h with globalID = new_eiid} in
      renumber_accesses_helper (result @ [h']) t edges eiids' next_eiid'
  | [] -> PipeGraph.Pair (result, renumber_edges eiids edges)

let renumber_accesses ops_edges =
  let ops, edges = ops_edges in
  renumber_accesses_helper [] ops edges IntMap.empty 0

let getAddress addr =
  try
    AddressMap.find addr !addressMap
  with Not_found ->
    addressMap :=
      AddressMap.add addr (AddressMap.cardinal !addressMap) !addressMap;
    AddressMap.find addr !addressMap

let getData data =
  try
    DataMap.find data !dataMap
  with Not_found ->
    dataMap := DataMap.add data (DataMap.cardinal !dataMap) !dataMap;
    DataMap.find data !dataMap

let access_of_line ghost_auto line old_uops old_edges =
  let d = Str.regexp "digraph" in
  try
    let _ = Str.search_forward d line 0 in
    true, [], []
  with
  Not_found ->
  let r = Str.regexp "eiid\\([0-9]+\\).*: \\(.*\\)..proc:\\([0-9]+\\)" in
  let rw_r_unlocked = Str.regexp "R\\([^*]+\\)=\\(.\\)" in
  let rw_r_locked   = Str.regexp "R\\([^*]+\\)\\*=\\(.\\)" in
  let rw_w_unlocked = Str.regexp "W\\([^*]+\\)=\\(.\\)" in
  let rw_w_locked   = Str.regexp "W\\([^*]+\\)\\*=\\(.\\)" in
  try
    let _ = Str.search_forward r line 0 in
    let eiid = int_of_string    (Str.matched_group 1 line)            in
    let rw   =                   Str.matched_group 2 line             in
    let proc = int_of_string    (Str.matched_group 3 line)            in
    let accesses =
      try
          let _ = Str.search_forward rw_r_locked rw 0 in
          let addr = getAddress (Str.matched_group 1 rw) in
          let data = getData    (Str.matched_group 2 rw) in
          if ghost_auto
          then
          [Read (["dirtybit"], {vtag=10+addr; vindex=1}, {ptag=PTETag addr; pindex=1},
              PipeGraph.PageTableEntry (addr, PipeGraph.PTag addr, {accessed=true; dirty=false}));
           Write (["dirtybit"], {vtag=10+addr; vindex=1}, {ptag=PTETag addr; pindex=1},
              PipeGraph.PageTableEntry (addr, PipeGraph.PTag addr, {accessed=true; dirty=true}));
           Read (["RMW"], {vtag=addr; vindex=0}, {ptag=PTag addr; pindex=0}, NormalData data);
           Read (["ptwalk"], {vtag=10+addr; vindex=1}, {ptag=PTETag addr; pindex=1},
              PipeGraph.PageTableEntry (addr, PipeGraph.PTag addr, {accessed=true; dirty=true}))]
          else
          [Read (["RMW"], {vtag=addr; vindex=0}, {ptag=PTag addr; pindex=0}, NormalData data)]
      with Not_found ->
      try
          let _ = Str.search_forward rw_r_unlocked rw 0 in
          let addr = getAddress (Str.matched_group 1 rw) in
          let data = getData    (Str.matched_group 2 rw) in
          if ghost_auto
          then
          [Read ([], {vtag=addr; vindex=0}, {ptag=PTag addr; pindex=0}, NormalData data);
           Read (["ptwalk"], {vtag=10+addr; vindex=1}, {ptag=PTETag addr; pindex=1},
              PipeGraph.PageTableEntry (addr, PipeGraph.PTag addr, {accessed=true; dirty=false}));
           Read (["ptwalk"], {vtag=10+addr; vindex=1}, {ptag=PTETag addr; pindex=1},
              PipeGraph.PageTableEntry (addr, PipeGraph.PTag addr, {accessed=true; dirty=true}))]
          else
          [Read ([], {vtag=addr; vindex=0}, {ptag=PTag addr; pindex=0}, NormalData data)]
      with Not_found ->
      try
        let _ = Str.search_forward rw_w_unlocked rw 0 in
        let addr = getAddress (Str.matched_group 1 rw) in
        let data = getData    (Str.matched_group 2 rw) in
        if ghost_auto
        then
        [Read (["dirtybit"], {vtag=10+addr; vindex=1}, {ptag=PTETag addr; pindex=1},
            PipeGraph.PageTableEntry (addr, PipeGraph.PTag addr, {accessed=true; dirty=false}));
         Write (["dirtybit"], {vtag=10+addr; vindex=1}, {ptag=PTETag addr; pindex=1},
            PipeGraph.PageTableEntry (addr, PipeGraph.PTag addr, {accessed=true; dirty=true}));
         Write ([], {vtag=addr; vindex=0}, {ptag=PTag addr; pindex=0}, NormalData data);
         Read (["ptwalk"], {vtag=10+addr; vindex=1}, {ptag=PTETag addr; pindex=1},
            PipeGraph.PageTableEntry (addr, PipeGraph.PTag addr, {accessed=true; dirty=true}))]
        else
        [Write ([], {vtag=addr; vindex=0}, {ptag=PTag addr; pindex=0}, NormalData data)]
      with Not_found ->
      try
        let _ = Str.search_forward rw_w_locked rw 0 in
        let addr = getAddress (Str.matched_group 1 rw) in
        let data = getData    (Str.matched_group 2 rw) in
        [Write (["RMW"], {vtag=addr; vindex=0}, {ptag=PTag addr; pindex=0}, NormalData data)]
      with Not_found ->
        [Fence [rw]]
      in
    let uop a b = {globalID=eiid; coreID=proc; threadID0=0; intraInstructionID0=a; access=b} in
    let new_uops = List.mapi uop accesses in
    false, old_uops @ new_uops, old_edges
  with Not_found -> try
    let r = Str.regexp "eiid\\([0-9]+\\) -> eiid\\([0-9]+\\).*label=\"\\([^\"]*\\)\"" in
    let _ = Str.search_forward r line 0 in
    let src   = int_of_string (Str.matched_group 1 line) in
    let dst   = int_of_string (Str.matched_group 2 line) in
    let label =                Str.matched_group 3 line  in
    let edge = PipeGraph.Pair (PipeGraph.Pair (src, dst), label) in
    false, old_uops, edge :: old_edges
  with Not_found -> false, old_uops, old_edges

let rec parse_herd_graph ghost_auto channel executions ops edges =
  try
    let line = input_line channel in
    let new_exec, ops', edges' = access_of_line ghost_auto line ops edges in
    match new_exec with
    | false -> parse_herd_graph ghost_auto channel executions ops' edges'
    | true  -> parse_herd_graph ghost_auto channel (executions @ [ops, edges]) ops' edges'
  with
    End_of_file ->
      Printf.printf "// Test has %d instructions\n" (length ops);
      map renumber_accesses (List.tl executions @ [ops, edges])

let rec check_if_allowed channel =
  try
    let line = input_line channel in
    try
      let _ = Str.search_forward (regexp "Never") line 0 in
      (Forbidden, line)
    with Not_found ->
    try
      let _ = Str.search_forward (regexp "Sometimes") line 0 in
      (Permitted, line)
    with Not_found ->
    try
      let _ = Str.search_forward (regexp "Always") line 0 in
      (Required, line)
    with Not_found -> check_if_allowed channel
  with
    End_of_file ->
      raise (Failure "Could not parse herd output")

let rec get_line_final_memory_values l n r =
  try
    let last = Str.search_forward (regexp "\\(\\[[w-z]\\]\\)=\\([0-9]\\)") l n in
    let addr = getAddress (Str.matched_group 1 l) in
    let data = getData    (Str.matched_group 2 l) in
    get_line_final_memory_values l (last + 1)
      (PipeGraph.Pair ({ptag=PTag addr; pindex=0}, PipeGraph.NormalData data) :: r)
  with Not_found ->
    try
      let last = Str.search_forward (regexp "\\([w-z]\\)=\\([0-9]\\)") l n in
      let addr = getAddress (Str.matched_group 1 l) in
      let data = getData    (Str.matched_group 2 l) in
      get_line_final_memory_values l (last + 1)
        (PipeGraph.Pair ({ptag=PTag addr; pindex=0}, PipeGraph.NormalData data) :: r)
    with Not_found ->
      r

let rec get_final_memory_values channel r =
  try
    let line = input_line channel in
    get_final_memory_values channel (get_line_final_memory_values line 0 r)
  with End_of_file ->
    r

let initial_page_table_entry s_vtag =
  let (_, vtag) = s_vtag in
  PipeGraph.Pair(
    {ptag=PipeGraph.PTETag vtag; pindex=1},
    PipeGraph.PageTableEntry (vtag, PipeGraph.PTag vtag,
      {accessed=true; dirty=true}))

let gen_random_char _ =
  let c =
    match Random.int(62) with
      n when n < 26 -> int_of_char 'a' + n
    | n when n < 52 -> int_of_char 'A' + n - 26
    | n             -> int_of_char '0' + n - 52 in
  char_of_int(c)

let gen_random_string _ =
  let c1 = gen_random_char() in
  let c2 = gen_random_char() in
  let c3 = gen_random_char() in
  let c4 = gen_random_char() in
  let c5 = gen_random_char() in
  let c6 = gen_random_char() in
  Printf.sprintf "%c%c%c%c%c%c" c1 c2 c3 c4 c5 c6

let rec gen_random_dir n =
  Random.self_init();
  match n with
  | 0 -> raise (Failure "could not generate temporary dir")
  | _ ->
    let path = Filename.get_temp_dir_name() ^ "/pipegraph" ^
      gen_random_string() in
    try
      Unix.mkdir path 0o700;
      Printf.eprintf "// tmpdir is %s\n" path;
      path
    with Unix.Unix_error (Unix.EEXIST, _, _) ->
      gen_random_dir (n-1)

let execute_herd ghost_auto herd_path litmus_test_path model =
  let testfile = Unix.openfile litmus_test_path [Unix.O_RDONLY] 0 in
  let testchannel = Unix.in_channel_of_descr testfile in
  let final_memory_values = get_final_memory_values testchannel [] in

  (* Create a pipe for herd to feed its output into *)
  let (pipe_read_end, pipe_write_end) = Unix.pipe() in

  (* Run herd once with "-show prop" to check whether it considers the
     proposed output to be legal or not *)
  let args = Array.of_list ["herd"; "-show"; "prop"; litmus_test_path] in
  let pid = Unix.create_process herd_path args
    Unix.stdin pipe_write_end Unix.stderr in
  Unix.close pipe_write_end;
  let _ =
    (match Unix.waitpid [] pid with
    | (_, Unix.WEXITED 0) -> true
    | (_, Unix.WEXITED 127) ->
        raise (Failure "herd: command not found.  Did you add it to your path?")
    | _ -> raise (Failure "herd 1")) in
  let channel = Unix.in_channel_of_descr pipe_read_end in
  let (allowed, line) = check_if_allowed channel in
  Printf.printf "// herd: allowed=%B: %s\n" (allowed == Permitted) line;

  (* Make a temporary directory to hold the generated graphs *)
  let pipegraph_path = gen_random_dir 5 in

  (* Run herd a second time with "-through all" to generate the graph(s) for
   the litmus test, whether they are permitted or not (PipeGraph will
   recheck). *)
  let null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
  let args2 = Array.of_list
    ["herd"; "-show"; "prop"; "-through"; "all"; "-o"; pipegraph_path;
       "-model"; model; litmus_test_path] in
  let pid2 = Unix.create_process herd_path args2
    (Unix.descr_of_in_channel stdin)
    null
    (Unix.descr_of_out_channel stderr) in
  let _ =
    (match Unix.waitpid [] pid2 with
    | (_, Unix.WEXITED 0) -> true
    | _ -> raise (Failure "herd 2")) in

  (* Read in the graph(s) produced by the second run of herd *)
  let herd_graph_filename = pipegraph_path ^ "/" ^
    (Filename.chop_extension (Filename.basename litmus_test_path)) ^ ".dot" in
  let herd_graph_descr = Unix.openfile herd_graph_filename [Unix.O_RDONLY] 0 in
  let programs =
    parse_herd_graph ghost_auto (Unix.in_channel_of_descr herd_graph_descr) [] [] [] in

  (* Calculate the initial state of the page table *)
  let initial_conditions =
    List.map initial_page_table_entry (AddressMap.bindings !addressMap) in

  (allowed, initial_conditions, final_memory_values, programs)
