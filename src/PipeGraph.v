(******************************************************************************)
(* Copyright (c) 2015 Daniel Lustig, Princeton University                     *)
(*                                                                            *)
(* Permission is hereby granted, free of charge, to any person obtaining a    *)
(* copy of this software and associated documentation files (the "Software"), *)
(* to deal in the Software without restriction, including without limitation  *)
(* the rights to use, copy, modify, merge, publish, distribute, sublicense,   *)
(* and/or sell copies of the Software, and to permit persons to whom the      *)
(* Software is furnished to do so, subject to the following conditions:       *)
(*                                                                            *)
(* The above copyright notice and this permission notice shall be included in *)
(* all copies or substantial portions of the Software.                        *)
(*                                                                            *)
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *)
(* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *)
(* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *)
(* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *)
(* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *)
(* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *)
(* DEALINGS IN THE SOFTWARE.                                                  *)
(******************************************************************************)

Require Import Arith.
Require Import List.
Require Import Ascii.
Require Import String.
Require Import PipeGraph.Debug.
Require Import PipeGraph.Util.
Require Import PipeGraph.StringUtil.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Graph.
Require Import PipeGraph.GraphvizCompressed.
Require Import PipeGraph.FOLPredicate.
Require Import PipeGraph.FOL.

Import ListNotations.

Require Extraction.
(* this line is necessary for successful compilation when using      *)
(*        The Coq Proof Assistant, version 8.8.1                     *)
(*        OCaml version 4.07.0                                       *)
(*        under Mac OS 10.12.6 (Sierra)                              *)
(* added by Vashti Galpin, Vashti.Galpin@ed.ac.uk, 26 October 2018   *)

Extraction Language OCaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => int [ "0" "(fun x -> x + 1)" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive ascii => char
[
"(* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

Extract Inductive string => "string" [ "(String.make 0 ' ')" " ( fun (a: (char * string)) -> (String.make 1 (Pervasives.fst a)) ^ (Pervasives.snd a) ) " ].
Extract Constant append => "( ^ )".
Extract Constant beq_string => "( fun (a:string) (b:string) -> a=b )".
Extract Constant string_prefix => "( fun (a:string) (b:string) ->
  try
    a = String.sub b 0 (String.length a)
  with
    Invalid_argument _ -> false
  )".
Extract Constant blt_nat => "( fun (a:int) (b:int) -> a < b )".
Extract Constant bgt_nat => "( fun (a:int) (b:int) -> a > b )".
Extract Constant blt_string => "( fun (a:string) (b:string) -> compare a b < 0 )".
Extract Constant substr => "( fun (n:int) (s:string) -> String.sub s n (String.length s - 4) )".

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant beq_nat => "( fun (a:int) (b:int) -> a=b )".
Extract Constant stringOfNat => "( fun (a:int) -> string_of_int a )".

Extract Constant MacroExpansionDepth => "( 100000 )".

Extract Constant List.length => "( List.length )".

Extract Constant PrintFlag => "( BackendLinux.printFlag )".
Extract Constant Printf => "( BackendLinux.printf )".
Extract Constant PrintfFlush => "( BackendLinux.printfFlush )".

Extract Constant TimeForStatusUpdate => "( BackendLinux.timeForStatusUpdate )".

(*
Extract Constant zero => "'λ000'".
Extract Constant one => "'λ001'".
Extract Constant shift =>
 "fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".
Extract Inlined Constant ascii_dec => "(=)".
*)
Extraction "PipeGraph.ml"
  GetAccessType
  BoundaryCondition Program GraphvizCompressedGraph
  FOLAxiom FOLImplies FOLIff MicroopQuantifier CoreQuantifier ThreadQuantifier
  FOLLookupPredicate_SS FOLLookupPredicate_S FOLLookupPredicate_E
  FOLLookupPredicate_lE FOLLookupPredicate_N FOLLookupPredicate_lN
  FOLLookupPredicate_SSS FOLLookupPredicate_IS
  FOLLookupPredicate_ADSS FOLLookupPredicate_ADS FOLLookupPredicate_IIIIS
  MicroarchitecturalComponent EvaluateUHBGraphs StageNames ExpectedResult.

