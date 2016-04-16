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
open PipeGraph
open Lexer
open Parser
open MicroarchLexer
open MicroarchParser

exception LitmusTestParsingFailure of (string * int * int)
exception ModelParsingFailure of (string * int * int)

let parse_litmus_test litmustest =
  (* (allowed, initial_conditions, programs) *)
  let lexbuf = Lexing.from_string litmustest in
  try
    let result = Parser.main Lexer.token lexbuf in
    Js.Unsafe.fun_call (Js.Unsafe.js_expr "hello")
      [|Js.Unsafe.inject (Js.string "Finished parsing litmus test\n")|];
    result
  with exn ->
    begin
      let curr = lexbuf.Lexing.lex_curr_p in
      let line = curr.Lexing.pos_lnum in
      let offset = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      let token = Lexing.lexeme lexbuf in
      Printf.printf "Litmus test parsing error: line %d, offset %d, token %s\n"
        line offset token;
      raise (LitmusTestParsingFailure("Litmus Test", line, offset));
    end

let rec n_copies n x =
  if n > 0 then (x :: n_copies (n-1) x) else [x]

let parse_uarch uarch_string num_cores =
  let lexbuf = Lexing.from_string uarch_string in
  try
    let pipeline = MicroarchParser.main MicroarchLexer.token lexbuf in
    Js.Unsafe.fun_call (Js.Unsafe.js_expr "hello")
      [|Js.Unsafe.inject (Js.string "Finished parsing (micro)architecture model\n")|];
    Js.Unsafe.fun_call (Js.Unsafe.js_expr "hello")
      [|Js.Unsafe.inject (Js.string "Calculating outcome...\n")|];
    n_copies num_cores pipeline
  with exn ->
    begin
      let curr = lexbuf.Lexing.lex_curr_p in
      let line = curr.Lexing.pos_lnum in
      let offset = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      let token = Lexing.lexeme lexbuf in
      Printf.printf "Microarchitecture parsing error: line %d, offset %d, token %s\n"
        line offset token;
      raise (ModelParsingFailure("Model", line, offset));
    end

let core_count p = fold_left max (map coreID p) 0

let first_observable_graph litmustest_string uarch_string =
  let (allowed, initial, programs) =
    parse_litmus_test litmustest_string in

  let processor =
    let num_cores =
      match programs with
      | p :: _ -> core_count (PipeGraph.fst (PipeGraph.fst p))
      | _ -> 0
      in
    parse_uarch uarch_string num_cores in

  let outcome =
    PipeGraph.evaluateUHBGraphs 100 processor programs initial in

  let (observable, graph) =
    match outcome with
    | PipeGraph.Some (PipeGraph.Pair (g, a)) ->
      let stage_names = PipeGraph.stageNames processor in
      let graph =
        PipeGraph.graphvizCompressedGraph "" stage_names g [] a in
      (true, List.fold_left (^) "" graph)
    | PipeGraph.None -> (false, "(not observable)")
  in

  (allowed, observable, graph)
