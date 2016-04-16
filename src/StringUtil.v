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

Import ListNotations.
Open Scope string_scope.

Definition tab := String (ascii_of_nat 9) "".
Definition newline := String (ascii_of_nat 10) "".
Definition quote := String (ascii_of_nat 34) "".

Definition stringOfNat (n : nat) : string :=
  (* Anything larger than 9 will be handled by OCaml's string_of_int during
   * extraction.  We don't need to worry about it here within Coq, it's
   * strictly cosmetic. *)
  String (ascii_of_nat (nat_of_ascii "0" + n)) "".

Definition StringOf
  (l : list string)
  : string :=
  fold_left append l "".

Fixpoint beq_string
  (s1 s2 : string)
  : bool :=
  match (s1, s2) with
  | (String h1 t1, String h2 t2) =>
      if beq_nat (nat_of_ascii h1) (nat_of_ascii h2)
      then beq_string t1 t2
      else false
  | (EmptyString, EmptyString) => true
  | _ => false
  end.

Fixpoint string_prefix
  (s1 s2 : string)
  : bool :=
  match (s1, s2) with
  | (String h1 t1, String h2 t2) =>
      if beq_nat (nat_of_ascii h1) (nat_of_ascii h2)
      then string_prefix t1 t2
      else false
  | (EmptyString, _) => true
  | _ => false
  end.

Fixpoint substr
  (n : nat)
  (s : string)
  : string :=
  match (s, n) with
  | (_, 0) => s
  | (EmptyString, S _) => ""
  | (String _ s', S n') => substr n' s'
  end.

Fixpoint find_string
  (s : string)
  (l : list string)
  : bool :=
  match l with
  | [] => false
  | h::t =>
    if beq_string s h
    then true
    else false
  end.
