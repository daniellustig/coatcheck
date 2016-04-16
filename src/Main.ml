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

open Printf
open Unix
open Arg
open BackendLinux
open PipeGraph
open HerdGraph
open Lexer
open Parser
open MicroarchLexer
open MicroarchParser

let input_filename = ref ""
let uarch_filename = ref ""
let extra_constraints_filename = ref ""
let do_reduction = ref true
let ghost_auto = ref false
let max_depth = ref 100

let update_input_filename s = input_filename := s
let update_output_filename s =
  let oc = open_out s in BackendLinux.outfile := oc
let update_uarch_filename s = uarch_filename := s
let update_extra_constraints_filename s = extra_constraints_filename := s
let update_max_depth n = max_depth := n
let update_verbosity n = BackendLinux.verbosity := n
let unknown_argument s = raise (Arg.Bad ("Unknown argument: " ^ s))

let parse_anon s = unknown_argument s

let speclist = [
  ("-i", Arg.String update_input_filename, "Input litmus test (.test format)");
  ("-o", Arg.String update_output_filename, "Output file (stdout otherwise)");
  ("-m", Arg.String update_uarch_filename, "Microarchitecture model file");
  ("-e", Arg.String update_extra_constraints_filename, "Extra constraints to add to the microarchitecture for this particular run");
  ("-r", Arg.Clear  do_reduction, "Don't perform transitive reduction");
  ("-d", Arg.Int    update_max_depth, "Max depth for DPLL search");
  ("-v", Arg.Int    update_verbosity, "Set verbosity level:
    0: Default; print final output
    1: + Print all solver decisions
    2: + Print steps between solver decisions
    3: + Print constraint trees
    4: same as 3 for now
    5: + Verbose
    6: + More Verbose
    7: + Really Verbose
    8: + Extremely Verbose")]

let _ = Arg.parse speclist parse_anon "PipeGraph"

let _ =
  if (String.length !input_filename = 0)
  then (Arg.usage speclist "PipeGraph";
    raise (Arg.Bad "No input file specified"))
  else if (String.length !uarch_filename = 0)
  then (Arg.usage speclist "PipeGraph";
    raise (Arg.Bad "No microarchitecture model file specified"))
  else ();;

let cleanGhostInstructions h =
  match (PipeGraph.getVirtualAddress h, PipeGraph.getPhysicalAddress h) with
  | (Some va, Some pa) -> [
    {h with intraInstructionID0=0};
    {h with intraInstructionID0=1;
       access=Read(["ptwalk"], {vtag=10+va.vtag; vindex=0},
         {ptag=PTETag va.vtag; pindex=0},
         PageTableEntry (va.vtag, pa.ptag,
           {accessed=true; dirty=false}))};
    {h with intraInstructionID0=2;
       access=Read(["ptwalk"], {vtag=10+va.vtag; vindex=0},
         {ptag=PTETag va.vtag; pindex=0},
         PageTableEntry (va.vtag, pa.ptag,
           {accessed=true; dirty=true}))}]
  | _ -> raise (Failure "Cleaning non-ghost")

let dirtyGhostInstructions h =
  match (PipeGraph.getVirtualAddress h, PipeGraph.getPhysicalAddress h) with
  | (Some va, Some pa) -> [
    {h with intraInstructionID0=0;
       access=Read(["dirtybit"], {vtag=10+va.vtag; vindex=0},
         {ptag=PTETag va.vtag; pindex=0},
         PageTableEntry (va.vtag, pa.ptag,
           {accessed=true; dirty=false}))};
    {h with intraInstructionID0=1;
       access=Write(["dirtybit"], {vtag=10+va.vtag; vindex=0},
         {ptag=PTETag va.vtag; pindex=0},
         PageTableEntry (va.vtag, pa.ptag,
           {accessed=true; dirty=true}))};
    {h with intraInstructionID0=2};
    {h with intraInstructionID0=3;
       access=Read(["ptwalk"], {vtag=10+va.vtag; vindex=0},
         {ptag=PTETag va.vtag; pindex=0},
         PageTableEntry (va.vtag, pa.ptag,
           {accessed=true; dirty=true}))}]
  | _ -> raise (Failure "Cleaning non-ghost")

let rec filter_ghosts_helper program =
  match program with
  | h::t ->
      (match (access h, PipeGraph.getAccessType h) with
      | (Fence _, _) -> h :: filter_ghosts_helper t
      | (FenceVA (_, _), _) -> h :: filter_ghosts_helper t
      | (Read _, []) ->
          cleanGhostInstructions h @ filter_ghosts_helper t
      | (Write _, []) ->
          dirtyGhostInstructions h @ filter_ghosts_helper t
      | (Read _, ["RMW"]) ->
          dirtyGhostInstructions h @ filter_ghosts_helper t
      | (Write _, ["RMW"]) ->
          {h with intraInstructionID0=0} :: filter_ghosts_helper t
      | (_, ["ptwalk"]) -> filter_ghosts_helper t
      | (_, ["dirtybit"]) -> filter_ghosts_helper t
      | (_, ["IRQCheck"]) -> h :: filter_ghosts_helper t
      | (_, ["IPIReceive"]) -> h :: filter_ghosts_helper t
      | (_, ["IPIAck"]) -> h :: filter_ghosts_helper t
      | (_, ["IRET"]) -> h :: filter_ghosts_helper t
      | _ -> raise (Failure "Unknown access type"))
  | [] -> []

let filter_ghosts x =
  PipeGraph.Pair (filter_ghosts_helper (PipeGraph.fst x), PipeGraph.snd x)

let (allowed, initial_conditions, programs) =
  if (String.length !input_filename > 0)
  then
    let file_descr = Unix.openfile !input_filename [Unix.O_RDONLY] 0 in
    let channel = Unix.in_channel_of_descr file_descr in
    let lexbuf = Lexing.from_channel channel in
    let (a, i, progs) = try
      Parser.main Lexer.token lexbuf
    with exn ->
      begin
        let curr = lexbuf.Lexing.lex_curr_p in
        let line = curr.Lexing.pos_lnum in
        let offset = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
        let token = Lexing.lexeme lexbuf in
        Printf.printf "Litmus test parsing error: line %d, offset %d, token %s\n"
          line offset token;
        raise (Failure "Parsing litmus test")
      end in
    (a, i, progs)
    (*
    if !ghost_auto
    then (a, i, List.map filter_ghosts progs)
    else (a, i, progs)
    *)
  else raise (Arg.Bad "Litmus test could not be parsed!")

let rec n_copies n x =
  if n > 0 then (x :: n_copies (n-1) x) else [x]

let parse_uarch filename num_cores =
  let file_descr = Unix.openfile filename [Unix.O_RDONLY] 0 in
  let channel = Unix.in_channel_of_descr file_descr in
  let lexbuf = Lexing.from_channel channel in
  try
    let pipeline = MicroarchParser.main MicroarchLexer.token lexbuf in
    n_copies num_cores pipeline
  with exn ->
    begin
      let curr = lexbuf.Lexing.lex_curr_p in
      let line = curr.Lexing.pos_lnum in
      let offset = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      let token = Lexing.lexeme lexbuf in
      Printf.printf "Microarchitecture parsing error: line %d, offset %d, token %s\n"
        line offset token;
      raise (Failure "Parsing microarchitecture")
    end

let program_length p = List.fold_left (+) 0 (map List.length p)

let core_count p = fold_left max (map coreID p) 0

let processor =
  let num_cores =
    match programs with
    | p :: _ -> core_count (PipeGraph.fst (PipeGraph.fst p))
    | _ -> 0
    in
  let baseline = parse_uarch !uarch_filename num_cores in
  let extras =
    if (String.length !extra_constraints_filename > 0)
    then parse_uarch !extra_constraints_filename num_cores
    else [] in
  baseline @ extras

let first_observable_graph programs initial =
  let graph =
    PipeGraph.evaluateUHBGraphs !max_depth processor programs initial in

  let observable =
    match graph with
    | PipeGraph.Some (PipeGraph.Pair (g, a)) ->
      (* let stage_names = PipeGraph.stageNames processor in
      let s = PipeGraph.graphvizCompressedGraph "" stage_names g [] in
      List.iter (Printf.fprintf oc "%s") s; *)
      true
    | PipeGraph.None -> false
  in

  let result_string =
    match (allowed, observable) with
    | (Permitted, true) -> "Allowed/Observable"
    | (Permitted, false) -> "Allowed/Not Observable (Stricter than necessary) !"
    | (Forbidden, true) -> "Forbidden/Observable (BUG) !"
    | (Forbidden, false) -> "Forbidden/Not observable"
    | (Required, true) -> "Required/Observable"
    | (Required, false) -> "Required/Not Observable (BUG) !"
    | (Unobserved, true) -> "Unobserved/Observable (Weaker than real HW?) !"
    | (Unobserved, false) -> "Unobserved/Not observable (Weaker than spec, same as real HW) !"
  in

  Printf.printf "// Input %s: %s\n" !input_filename result_string

let _ = first_observable_graph programs initial_conditions;

print_string "// Done!\n"

