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

Require Import List.
Require Import Arith.
Require Import String.
Require Import Ascii.
Require Import PipeGraph.StringUtil.

Import ListNotations.
Open Scope string_scope.

(** * Debugging functions *)

Definition PrintFlag (n : nat) := false.

(** ** [Printf] *)
(** The semantics of [Printf] are a little weird due to the Coq to OCaml
extraction process.  The argument [a] is returned by the function, and this
returned value must be used by some later function to ensure that the [Printf]
doesn't get optimized away during extraction. *)
Definition Printf
  {A : Type}
  (x : A)
  (s : string)
  : A :=
  x.

Definition PrintfFlush
  {A : Type}
  (x : A)
  (s : string)
  : A :=
  x.

Definition PrintlnFlush
  {A : Type}
  (x : A)
  (l : list string)
  : A :=
  PrintfFlush x (StringOf (app l [newline])).

Definition Println
  {A : Type}
  (x : A)
  (l : list string)
  : A :=
  Printf x (StringOf (l ++ [newline])).

Definition Comment
  {A : Type}
  (x : A)
  (l : list string)
  : A :=
  Println x ("// " :: l).

Definition CommentFlush
  {A : Type}
  (x : A)
  (l : list string)
  : A :=
  PrintlnFlush x ("// " :: l).

(** ** [Warning] *)
(** The semantics of [Warning] are a little weird due to the Coq to OCaml
extraction process.  The argument [a] is returned by the function, and this
returned value must be used by some later function to ensure that the [Warning]
doesn't get optimized away during extraction. *)
Definition Warning
  {A : Type}
  (x : A)
  (ss : list string)
  : A :=
  PrintfFlush x (StringOf ((newline :: "WARNING: " :: ss) ++ [newline; newline])).

Definition MacroExpansionDepth := 100.

Definition TimeForStatusUpdate
  (n : nat)
  : bool :=
  false.
