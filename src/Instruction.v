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

Require Import Bool.
Require Import String.
Require Import Arith.
Require Import List.
Require Import PipeGraph.Debug.
Require Import PipeGraph.StringUtil.

(** ** Basic Type Definitions *)
Definition InstID := nat.
Definition ThreadID := nat.
Definition IntraInstructionID := nat.

Definition VirtualTag := nat.

Definition beq_vtag := beq_nat.

Inductive PhysicalTag : Set :=
| PTag : nat -> PhysicalTag
| PTETag : VirtualTag -> PhysicalTag
| APICTag : string -> nat -> PhysicalTag.

Definition beq_ptag
  (a b : PhysicalTag)
  : bool :=
  match (a, b) with
  | (PTag a1, PTag b1) => beq_nat a1 b1
  | (PTETag a1, PTETag b1) => beq_nat a1 b1
  | (APICTag a1 a2, APICTag b1 b2) => andb (beq_string a1 b1) (beq_nat a2 b2)
  | _ => false
  end.

Definition Index := nat.

Record VirtualAddress : Set := VA {
  vtag : VirtualTag;
  vindex : Index
}.

Definition beq_vaddr
  (a b : VirtualAddress)
  : bool :=
  match (a, b) with
  | (VA a1 a2, VA b1 b2) => andb (beq_nat a1 b1) (beq_nat a2 b2)
  end.

Record PhysicalAddress : Set := PA {
  ptag : PhysicalTag;
  pindex : Index
}.

Definition beq_paddr
  (a b : PhysicalAddress)
  : bool :=
  match (a, b) with
  | (PA a1 a2, PA b1 b2) => andb (beq_ptag a1 b1) (beq_nat a2 b2)
  end.

Record PTEStatus : Set := pte {
  accessed : bool;
  dirty : bool
}.

Definition beq_pte_status
  (a b : PTEStatus)
  : bool :=
  match (a, b) with
  | (pte a1 a2, pte b1 b2) => andb (eqb a1 b1) (eqb a2 b2)
  end.

Inductive AccessedStatus : Set :=
| Accessed : AccessedStatus
| NotAccessed : AccessedStatus
| AccessedDontCare : AccessedStatus.

Definition StringOfAccessedStatus
  (s : AccessedStatus)
  : string :=
  match s with
  | Accessed => "acc"
  | NotAccessed => "!acc"
  | AccessedDontCare => "?acc"
  end.

Inductive DirtyStatus : Set :=
| Dirty : DirtyStatus
| NotDirty : DirtyStatus
| DirtyDontCare : DirtyStatus.

Definition StringOfDirtyStatus
  (s : DirtyStatus)
  : string :=
  match s with
  | Dirty => "dirty"
  | NotDirty => "!dirty"
  | DirtyDontCare => "?dirty"
  end.

Definition match_pte_status
  (s : PTEStatus)
  (a : AccessedStatus)
  (d : DirtyStatus)
  : bool :=
  match (accessed s, a, dirty s, d) with
  | (true, Accessed     , true, Dirty) => true
  | (false, NotAccessed , true, Dirty) => true
  | (_, AccessedDontCare, true, Dirty) => true
  | (true, Accessed     , false, NotDirty) => true
  | (false, NotAccessed , false, NotDirty) => true
  | (_, AccessedDontCare, false, NotDirty) => true
  | (true, Accessed     , _, DirtyDontCare) => true
  | (false, NotAccessed , _, DirtyDontCare) => true
  | (_, AccessedDontCare, _, DirtyDontCare) => true
  | _ => false
  end.

Import ListNotations.

Definition StringOfPTEStatus
  (s : PTEStatus)
  : string :=
  match s with
  | pte a d => StringOf [
      if a then "a_" else "na_";
      if d then "d" else "nd"]
  end.

Inductive Data : Set :=
| UnknownData : Data
| NormalData : nat -> Data
| PageTableEntry : VirtualTag -> PhysicalTag -> PTEStatus -> Data
| OtherData : string -> nat -> Data.

Definition beq_pte
  (e : Data)
  (v : VirtualTag)
  (p : PhysicalTag)
  (a : AccessedStatus)
  (d : DirtyStatus)
  : bool :=
  match e with
  | PageTableEntry v' p' s' =>
      andb (andb (beq_vtag v v') (beq_ptag p p'))
        (match_pte_status s' a d)
  | _ => false
  end.

Definition beq_data
  (a b : Data)
  : bool :=
  match (a, b) with
  | (NormalData a', NormalData b') => beq_nat a' b'
  | (PageTableEntry a1 a2 a3, PageTableEntry b1 b2 b3) =>
      andb (andb (beq_nat a1 b1) (beq_ptag a2 b2))
        (beq_pte_status a3 b3)
  | (OtherData a1 a2, OtherData b1 b2) =>
      andb (beq_string a1 b1) (beq_nat a2 b2)
  | _ => false
  end.

Definition BoundaryCondition := (PhysicalAddress * Data) % type.

(** ** Instructions *)

(** *** [MemoryAccess] *)
(** A [MemoryAccess] is the part of the [Microop] data structure representing
interaction with the memory system. *)
Inductive MemoryAccess : Set :=
| Read     : list string -> VirtualAddress -> PhysicalAddress -> Data -> MemoryAccess
| Write    : list string -> VirtualAddress -> PhysicalAddress -> Data -> MemoryAccess
| Fence    : list string -> MemoryAccess
| FenceVA  : list string -> VirtualAddress -> MemoryAccess
(* LL/SC, etc. *).

(** *** [Microop] *)
(** A [Microop] is either an instruction or part of an instruction.  Each
[Microop] has a globally unique ID [globalID], a thread ID [threadID], an
intra-instruction ID [intraInstructionID] (for when a single macroinstruction
has multiple microops), and a [MemoryAccess] [access] describing the memory
semantics. *)
Record Microop : Set := mkMicroop {
  globalID : InstID;
  coreID : nat;
  threadID : ThreadID;
  intraInstructionID : IntraInstructionID;
  access : MemoryAccess
}.

Definition GetAccessType
  (uop : Microop)
  : list string :=
  match uop with
  | mkMicroop _ _ _ _ (Read     t _ _ _) => t
  | mkMicroop _ _ _ _ (Write    t _ _ _) => t
  | mkMicroop _ _ _ _ (Fence    t      ) => t
  | mkMicroop _ _ _ _ (FenceVA  t _    ) => t
  end.

Definition GetVirtualAddress
  (uop : Microop)
  : option VirtualAddress :=
  match uop with
  | mkMicroop _ _ _ _ (Read     _ a _ _) => Some a
  | mkMicroop _ _ _ _ (Write    _ a _ _) => Some a
  | mkMicroop _ _ _ _ (FenceVA  _ a    ) => Some a
  | _ => None
  end.

Definition GetVirtualTag
  (uop : Microop)
  : option VirtualTag :=
  match GetVirtualAddress uop with
  | Some (VA t _) => Some t
  | _ => None
  end.

Definition GetIndex
  (uop : Microop)
  : option Index :=
  match GetVirtualAddress uop with
  | Some (VA _ i) => Some i
  | _ => None
  end.

Definition GetPhysicalAddress
  (uop : Microop)
  : option PhysicalAddress :=
  match uop with
  | mkMicroop _ _ _ _ (Read     _ _ a _) => Some a
  | mkMicroop _ _ _ _ (Write    _ _ a _) => Some a
  | _ => None
  end.

Definition GetPhysicalTag
  (uop : Microop)
  : option PhysicalTag :=
  match GetPhysicalAddress uop with
  | Some (PA t _) => Some t
  | _ => None
  end.

Definition GetData
  (uop : Microop)
  : option Data :=
  match uop with
  | mkMicroop _ _ _ _ (Read     _ _ _ d) => Some d
  | mkMicroop _ _ _ _ (Write    _ _ _ d) => Some d
  | _ => None
  end.

(** *** [SameVirtualAddress] *)
Definition SameVirtualAddress
  (x y : Microop)
  : bool :=
  match (GetVirtualAddress x, GetVirtualAddress y) with
  | (Some ax, Some ay) => beq_vaddr ax ay
  | _ => false
  end.

Definition SameVirtualTag
  (x y : Microop)
  : bool :=
  match (GetVirtualTag x, GetVirtualTag y) with
  | (Some ax, Some ay) => beq_vtag ax ay
  | _ => false
  end.

(** *** [SamePhysicalAddress] *)
Definition SamePhysicalAddress
  (x y : Microop)
  : bool :=
  match (GetPhysicalAddress x, GetPhysicalAddress y) with
  | (Some ax, Some ay) => beq_paddr ax ay
  | _ => false
  end.

Definition SamePhysicalTag
  (x y : Microop)
  : bool :=
  match (GetPhysicalTag x, GetPhysicalTag y) with
  | (Some ax, Some ay) => beq_ptag ax ay
  | _ => false
  end.

Definition SameIndex
  (x y : Microop)
  : bool :=
  match (GetIndex x, GetIndex y) with
  | (Some ax, Some ay) => beq_nat ax ay
  | _ => false
  end.

(** *** [SameData] *)
Definition SameData
  (x y : Microop)
  : bool :=
  match (GetData x, GetData y) with
  | (Some ax, Some ay) => beq_data ax ay
  | _ => false
  end.

(** *** [beq_uop] *)
(** Boolean equality check for two [Microop]s. *)
Definition beq_uop
  (a b : Microop)
  : bool :=
  andb (beq_nat (globalID a) (globalID b))
    (beq_nat (intraInstructionID a) (intraInstructionID b)).

(** ** [Thread]s and [Program]s *)
(** A [Thread] is a list of [Microop]s.  A [Program] is a list of [Thread]s. *)
Definition Thread : Set := list Microop.

Definition Program : Set := list Thread.

Definition VAPASameTagAndIndex
  (v : VirtualAddress)
  (p : PhysicalAddress)
  : bool :=
  match (v, p) with
  | (VA vt vi, PA (PTag pt) pi) =>
      andb (beq_nat vt pt) (beq_nat vi pi)
  | _ => false
  end.

