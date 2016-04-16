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
Require Import PipeGraph.Debug.

Import ListNotations.

(** ** Generally useful functions *)

(** *** [bgt_nat] *)
Fixpoint bgt_nat
  (a b : nat)
  : bool :=
  match (a, b) with
  | (S a', S b') => bgt_nat a' b'
  | (S a', O   ) => true
  | (O   , S b') => false
  | (O   , O   ) => false
  end.

Definition blt_nat
  (a b : nat)
  : bool :=
  bgt_nat b a.

(** *** [Range] *)
(** Generate the list [0, 1, ..., n-1] *)
Fixpoint RangeHelper
  (n : nat)
  (l : list nat)
  : list nat :=
  match n with
  | O => l
  | S n' => RangeHelper n' (n' :: l)
  end.

Definition Range
  (n : nat)
  : list nat :=
  RangeHelper n [].

Module RangeExample.

Example e1 : Range 3 = [0; 1; 2].
Proof.
auto.
Qed.

End RangeExample.

(** *** [Map] *)
(** Tail recursive version of [map]. *)
Fixpoint MapHelper
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (l' : list B)
  : list B :=
  match l with
  | h::t => MapHelper f t (f h :: l')
  | [] => rev' l'
  end.

Definition Map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  : list B :=
  MapHelper f l [].

Fixpoint app_rev
  {A : Type}
  (a : list A)
  (b : list A)
  : list A :=
  match b with
  | [] => a
  | h::t => app_rev (h::a) t
  end.

Definition app_tail
  {A : Type}
  (a b : list A)
  : list A :=
  app_rev b (rev' a).

(** *** [removeb] *)
(** Remove every element [x] of list [l1] for which [f x] is [true]. *)
Fixpoint removeb_helper
  {A : Type}
  (f : A -> bool)
  (l1 : list A)
  (l2 : list A)
  : list A :=
  match l1 with
  | [] => l2
  | x::tl =>
      if (f x) then removeb_helper f tl l2 else removeb_helper f tl (x::l2)
  end.

Definition removeb
  {A : Type}
  (f : A -> bool)
  (l : list A)
  : list A :=
  removeb_helper f (rev' l) [].

(** ** Cross Product *)

(** *** [CrossProduct] *)
(** Given: a list of lists of choices.  The first list of the input is the set
of choices for the first item, the second list of the input is the set of
choices for the second item, etc.  Produce: a list of the cross product of
choices, one from each list of the input. *)
Definition CrossProductHelper
  {A : Type}
  (heads : list A)
  (tails : list (list A))
  : list (list A) :=
  let f x := Map (cons x) tails in
  let all := Map f heads in
  fold_left (app_tail (A:=_)) all [].

Fixpoint CrossProduct
  {A : Type}
  (l : list (list A))
  : list (list A) :=
  match l with
  | [] => []
  | h::t =>
      match t with
      | [] => fold_left (app_tail (A:=_)) (Map (fun x => [[x]]) h) []
      | _  => CrossProductHelper h (CrossProduct t)
      end
  end.

(** *** [CrossProduct] Examples *)
Module CrossProductExamples.

Example e1:
  CrossProduct [[1; 2]; [3; 4]] = [[1; 3]; [1; 4]; [2; 3]; [2; 4]].
Proof.
auto.
Qed.

Example e2:
  CrossProduct [[]; [1; 2]; [3; 4]] = [].
Proof.
auto.
Qed.

Example e3:
  let a : list (list nat) := [[]] in
  CrossProduct a = [].
Proof.
auto.
Qed.

End CrossProductExamples.

