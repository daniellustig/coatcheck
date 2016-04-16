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
Require Import PipeGraph.Debug.
Require Import PipeGraph.Util.
Require Import PipeGraph.StringUtil.
Require Import PipeGraph.Instruction.

Import ListNotations.
Open Scope list_scope.

(** ** Basic Type Definitions *)

(** *** [Location] *)
(** A [Location] is an (x,y) coordinate representing a particular location
within a microarchitecture.  x represents the pipeline number, and y represents
the pipeline stage (or equivalent) within that pipeline. *)
Definition Location := (nat * nat) % type.

(** *** [GraphNode] and [GraphEdge] *)
(** A [GraphNode] represents a [Microop] at a particular [Location] in the
microarchitecture. *)
Definition GraphNode := (Microop * Location) % type.
(** A [GraphEdge] is a directed edge between two [GraphNode]s. *)
Definition GraphEdge := (GraphNode * GraphNode * string * string) % type.

(** *** [beq_loc] *)
Definition beq_loc
  (a b : Location)
  : bool :=
  match (a, b) with
  | ((a0, a1), (b0, b1)) => andb (beq_nat a0 b0) (beq_nat a1 b1)
  end.

(** *** [beq_node] *)
(** Boolean comparison of [GraphNode]s. *)
Definition beq_node
  (a b : GraphNode)
  : bool :=
  match (a, b) with
  | ((i0, (p0, l0)), (i1, (p1, l1))) =>
      andb
      (* beq_uop i0 i1 *)
      (andb (beq_nat (globalID i0) (globalID i1))
        (beq_nat (intraInstructionID i0) (intraInstructionID i1)))
      (andb (beq_nat p0 p1) (beq_nat l0 l1))
  end.

(* Simplify the code extracted for beq_node by inlining beq_uop, but make
* sure that we don't change beq_uop unexpectedly. *)
Lemma beq_uop_is_beq_uop:
  forall a b, beq_uop a b =
  andb (beq_nat (globalID a) (globalID b))
    (beq_nat (intraInstructionID a) (intraInstructionID b)).
Proof.
  auto.
Qed.

(** *** [beq_edge] *)
(** Boolean comparison of [GraphEdge]s.  Labels not compared. *)
Definition beq_edge
  (a b : GraphEdge)
  : bool :=
  match (a, b) with
  | ((a1, a2, alabel, acolor), (b1, b2, blabel, bcolor)) =>
      andb (beq_node a1 b1) (beq_node a2 b2)
  end.

Definition KnownAddresses := [
  (0, "x"); (1, "y"); (2, "z"); (3, "w")].

Fixpoint AddressString
  (l : list (nat * string))
  (a : nat)
  : string :=
  match l with
  | (h1, h2)::t =>
      if beq_nat h1 a
      then h2
      else AddressString t a
  | _ => StringOf ["addr"; stringOfNat a]
  end.

Definition GraphvizStringOfVirtualAddress
  (a : VirtualAddress)
  : string :=
  match a with
  | VA t i => StringOf [
      AddressString KnownAddresses t;
      if beq_nat 0 i
      then ""
      else StringOf ["."; stringOfNat i]]
  end.

Definition GraphvizStringOfPhysicalTag
  (t : PhysicalTag)
  : string :=
  match t with
  | PTag t' => stringOfNat t'
  | PTETag t' => StringOf ["PTEfor"; stringOfNat t']
  | APICTag s t' => StringOf ["APICTag_"; s; "_"; stringOfNat t']
  end.

Definition GraphvizStringOfPhysicalAddress
  (a : PhysicalAddress)
  : string :=
  match a with
  | PA t i =>
      StringOf ["PA"; GraphvizStringOfPhysicalTag t; stringOfNat i]
  end.

Definition GraphvizStringOfData
  (d : Data)
  : string :=
  match d with
  | UnknownData => "unk"
  | NormalData n => stringOfNat n
  | PageTableEntry v p s => StringOf [
      "PTE_"; stringOfNat v; "_"; GraphvizStringOfPhysicalTag p; "_";
      StringOfPTEStatus s]
  | OtherData t n => StringOf [t; "_"; stringOfNat n]
  end.

Definition GraphvizStringOfMemoryAccess
  (divider : string)
  (a : MemoryAccess)
  : string :=
  match a with
  | Read t v p d => StringOf ["Read"; divider;
      fold_left (fun a b => StringOf [a; b; divider]) t "";
      GraphvizStringOfVirtualAddress v; divider;
      if VAPASameTagAndIndex v p
      then ""
      else StringOf [GraphvizStringOfPhysicalAddress p; divider];
      GraphvizStringOfData d]
  | Write t v p d => StringOf ["Write"; divider;
      fold_left (fun a b => StringOf [a; b; divider]) t "";
      GraphvizStringOfVirtualAddress v; divider;
      if VAPASameTagAndIndex v p
      then ""
      else StringOf [GraphvizStringOfPhysicalAddress p; divider];
      GraphvizStringOfData d]
  | Fence n => fold_left (fun a b => StringOf [a; b; divider]) n ""
  | FenceVA n v => StringOf [
      fold_left (fun a b => StringOf [a; b; divider]) n "";
      divider; GraphvizStringOfVirtualAddress v]
  end.

Definition GraphvizShortStringOfGraphNode
  (n : GraphNode)
  : string :=
  match n with
  | (mkMicroop g c t n a, (p, l)) =>
      StringOf [
          "n";
          stringOfNat g;
          "_";
          stringOfNat c;
          "_";
          stringOfNat t;
          "_";
          stringOfNat n;
          "_";
          GraphvizStringOfMemoryAccess "_" a;
          "_at_";
          stringOfNat p;
          "_";
          stringOfNat l
      ]
  end.

Definition StringOfGraphEdge
  (e : GraphEdge)
  : string :=
  match e with
  | (s, d, label, color) =>
    StringOf [
      tab; GraphvizShortStringOfGraphNode s; " -> ";
      GraphvizShortStringOfGraphNode d; " [label="; quote; label; quote;
      ";color="; color; "]"]
  end.

Definition ShortStringOfGraphNode
  (n : GraphNode)
  : string :=
  match n with
  | (s1, (s2, s3)) =>
      StringOf ["("; stringOfNat (globalID s1); ", ("; stringOfNat s2; ", ";
        stringOfNat s3; "))"]
  end.

Definition ShortStringOfGraphEdge
  (e : GraphEdge)
  : string :=
  match e with
  | (s, d, l, c) =>
      StringOf [ShortStringOfGraphNode s; " --"; l; "--> ";
        ShortStringOfGraphNode d]
  end.

(** ** Helper Functions *)

(** *** [ReverseEdge] *)
(** Return the edge pointing the opposite direction *)
Definition ReverseEdge
  (e : GraphEdge)
  : GraphEdge :=
  match e with
  | (s, d, l, c) =>
      (d, s, l, c)
  end.

(** * Topological Sort *)

(** ** [AdjacencyList] *)
Definition AdjacencyList := list (GraphNode * list (GraphNode * string * string)).

(** ** [AdjacencyList] Operations *)

(** *** [AdjacencyListAddEdgeHelper] *)
(** Given an adjacency list [l_new], add the edge [(s, d, label)] *)
Fixpoint AdjacencyListAddEdgeHelper
  (s d : GraphNode)
  (label color : string)
  (l_old l_new : AdjacencyList)
  : bool * AdjacencyList :=
  match l_new with
  | (h_s, h_ds)::t =>
      if beq_node s h_s
      then (true, app_rev l_old ((h_s, (d, label, color) :: h_ds) :: t))
      else AdjacencyListAddEdgeHelper s d label color ((h_s, h_ds) :: l_old) t
  | [] => (true, (s, [(d, label, color)]) :: l_old)
  end.

(** *** [AdjacencyListAddEdge] *)
(** Add a [GraphEdge] to an [AdjacencyList], and report whether the edge was
new *)
Definition AdjacencyListAddEdge
  (l : AdjacencyList)
  (e : GraphEdge)
  : bool * AdjacencyList :=
  match e with
  | (s, d, label, color) =>
      AdjacencyListAddEdgeHelper s d label color [] l
  end.

(** *** [AdjacencyListFromEdges] *)
(** Create an [AdjacencyList] from a list of [GraphEdge]s *)
Fixpoint AdjacencyListFromEdges
  (l : list GraphEdge)
  : AdjacencyList :=
  fold_left (fun a b => snd (AdjacencyListAddEdge a b)) l [].

(** ** [NodesFromEdges] *)
(** Given a list of [GraphEdge]s, return the list of [GraphNode]s used in the
edges, without duplicates. *)
Fixpoint NodesFromEdgesHelper
  (l : list GraphEdge)
  (r : list GraphNode)
  : list GraphNode :=
  match l with
  | (h1, h2, label, color)::t =>
      let r1 :=
        match find (beq_node h1) r with
        | Some _ => r
        | None => h1 :: r
        end in
      let r2 :=
        match find (beq_node h2) r1 with
        | Some _ => r1
        | None => h2 :: r1
        end in
      NodesFromEdgesHelper t r2
  | [] => r
  end.

Definition NodesFromEdges
  (l : list GraphEdge)
  : list GraphNode :=
  NodesFromEdgesHelper l [].

(** *** [EdgesFromAdjacencyList] *)
(** Return the list of [GraphEdge]s in an [AdjacencyList] *)
Fixpoint EdgesFromAdjacencyList
  (l : AdjacencyList)
  : list GraphEdge :=
  let f x :=
    let g y :=
      match y with
      | (d, label, color) => (fst x, d, label, color)
      end in
    Map g (snd x) in
  let l' := Map f l in
  fold_left (app_tail (A:=_)) l' [].

(** *** [NodesFromAdjacencyList] *)
(** Return the set of [GraphNode]s used in an [AdjacencyList] *)
Definition NodesFromAdjacencyList
  (l : AdjacencyList)
  : list GraphNode :=
  NodesFromEdges (EdgesFromAdjacencyList l).

(** **** [AdjacencyListFindHelper] *)
(** Return the label of any matching edge, but prefer anything over "TC" *)
Fixpoint AdjacencyListFindHelper
  (l : list (GraphNode * string * string))
  (found_tc : bool)
  (found_not : option (string * string))
  : option (string * string) :=
  match (l, found_tc, found_not) with
  | ((_, label, color) :: t, _, _) =>
      if beq_string "TC" label
      then AdjacencyListFindHelper t true found_not
      else if string_prefix "NOT_" label
      then AdjacencyListFindHelper t found_tc (Some (label, color))
      else Some (label, color)
  | ([], _    , Some (label, color)) => Some (label, color)
  | ([], true , None) => Some ("TC", "gray")
  | ([], false, None) => None
  end.

(** *** [AdjacencyListFind] *)
(** Return the label of the edge [(s, d)] if it is contained in the
[AdjacencyList], and [None] otherwise. *)
Fixpoint AdjacencyListFind
  (l : AdjacencyList)
  (s d : GraphNode)
  : option (string * string) :=
  match find (fun x => beq_node s (fst x)) l with
  | Some l' =>
      let matches := filter (fun x => beq_node (fst (fst x)) d) (snd l') in
      AdjacencyListFindHelper matches false None
  | None => None
  end. 

(** Add a [GraphEdge] to an [AdjacencyList] if it isn't already present. *)
Definition AdjacencyListAddEdgeCheckDups
  (l : AdjacencyList)
  (e : GraphEdge)
  : AdjacencyList :=
  match AdjacencyListFind l (fst (fst (fst e))) (snd (fst (fst e))) with
  | Some (label, _) =>
      if beq_string (snd (fst e)) label
      then l
      else snd (AdjacencyListAddEdge l e)
  | None => snd (AdjacencyListAddEdge l e)
  end.

(** *** [AdjacencyListGetDsts] *)
(** Return the set of [GraphNode]s reachable from the given source node, or the
empty list if not found. *)
Fixpoint AdjacencyListGetDsts
  (l : AdjacencyList)
  (s : GraphNode)
  : list (GraphNode * string * string) :=
  match find (fun x => beq_node s (fst x)) l with
  | Some l' => snd l'
  | None => []
  end. 

(** *** [AdjacencyListRemove] *)
(** Remove the node [(s, d)] from an [AdjacencyList] *)
Fixpoint AdjacencyListRemoveHelper
  (s : GraphNode)
  (ds : list (GraphNode * string * string))
  (d : GraphNode)
  : GraphNode * list (GraphNode * string * string) :=
  (s, removeb (fun x => beq_node d (fst (fst x))) ds).

Fixpoint AdjacencyListRemove
  (l : AdjacencyList)
  (s d : GraphNode)
  : AdjacencyList :=
  match l with
  | (h1, h2)::t =>
      if beq_node s h1
      then AdjacencyListRemoveHelper h1 h2 d :: t
      else (h1, h2) :: AdjacencyListRemove t s d
  | [] => []
  end.

(** *** [AdjacencyListRemoveSource] *)
(** Remove all edges originating from [s] in the [AdjacencyList] *)
Fixpoint AdjacencyListRemoveSource
  (l : AdjacencyList)
  (s : GraphNode)
  : AdjacencyList :=
  match l with
  | (h1, h2)::t =>
      if beq_node s h1
      then t
      else (h1, h2) :: AdjacencyListRemoveSource t s
  | [] => []
  end.

(** *** [AdjacencyListFilter] *)
(** Remove all edges in the [AdjacencyList] for which
[f (s, d, label) = false], and return the resulting list of edges. *)
Fixpoint AdjacencyListFilterHelper
  (f : GraphEdge -> bool)
  (s : GraphNode)
  (d : list (GraphNode * string * string))
  : list GraphEdge :=
  match d with
  | (h, label, color)::t =>
      if f (s, h, label, color)
      then (s, h, label, color) :: AdjacencyListFilterHelper f s t
      else                         AdjacencyListFilterHelper f s t
  | [] => []
  end.

Fixpoint AdjacencyListFilter
  (f : GraphEdge -> bool)
  (l : AdjacencyList)
  : list GraphEdge :=
  match l with
  | (hs, hd)::t =>
      AdjacencyListFilterHelper f hs hd ++ AdjacencyListFilter f t
  | [] => []
  end.

(** ** Topological Sort *)

(**
<<
Pseudocode from Wikipedia, attributed to Kahn 1962.

     L = Empty list that will contain the sorted elements
     S = Set of all nodes with no incoming edges
 1   while S is non-empty do
 1       remove a node n from S
 1       add n to tail of L
   2     for each node m with an edge e from n to m do
   2         remove edge e from the graph
   2         if m has no other incoming edges then
   2             insert m into S
 1   if graph has edges then
 1       return error (graph has at least one cycle)
 1   else 
 1       return L (a topologically sorted order)

 1: [TopsortHelper]
 2: [TopsortHelperProcessNode]
>>
*)

(** a Topological Sort can return three types of [TopsortResult]: a total
order (returned here in reverse order, for the convenience of the
[TransitiveClosure] algorithm), a cycle (in which case no topological sort is
possible), or an error. *)
Inductive TopsortResult : Set :=
| ReverseTotalOrder : list GraphNode -> TopsortResult
| Cyclic : list GraphEdge -> TopsortResult
| Abort : nat -> TopsortResult.

(** *** [SourceNodes] *)
(** Return the list of [GraphNode]s from [srcs] which have no incoming edges
listed in [l]. *)
Fixpoint SourceNodes
  (l : list GraphEdge)
  (srcs : list GraphNode)
  : list GraphNode :=
  match l with
  | (h1, h2, label, color)::t => SourceNodes t (removeb (beq_node h2) srcs)
  | [] => srcs
  end.

(** *** [TopsortHelperProcessNode] *)
(** For each node m with an edge ([n], m), remove ([n], m) from the list of
edges, and then if m is left with no more incoming edges, add it to [s]. *)
Fixpoint TopsortHelperProcessNode
  (l : list GraphNode)
  (s : list GraphNode)
  (n : GraphNode)
  (incoming : AdjacencyList)
  : AdjacencyList * list GraphNode :=
  match l with
  | h::t => 
      (* Remove edge (h, n) *)
      let incoming' := AdjacencyListRemove incoming h n in
      match AdjacencyListGetDsts incoming' h with
      | [] => (* n has no more incoming edges *)
          TopsortHelperProcessNode t (h :: s) n incoming'
      | _  => (* n still has more incoming edges *)
          TopsortHelperProcessNode t       s  n incoming'
      end
  | [] => (incoming, s)
  end.

(** *** [TopsortHelper] *)
(** Perform the outer loop of the topological sort algorithm *)
Fixpoint TopsortHelper
  (i : nat) (* Termination criterion *)
  (l s : list GraphNode)
  (outgoing incoming : AdjacencyList)
  : TopsortResult :=
  match (i, s) with
  | (S i', h::t) =>
      (* Process the node [h] at the head of [s] *)
      let f x := fst (A:=_) (B:=_) (fst x) in
      let dsts := Map f (AdjacencyListGetDsts outgoing h) in
      let (incoming', s') :=
        TopsortHelperProcessNode dsts t h incoming in
      (* Remove [h] from the [AdjacencyList] *)
      let outgoing' := AdjacencyListRemoveSource outgoing h in
      (* Add [h] to the front of [l] (which is in reverse order *)
      let l' := h :: l in
      (* Recurse *)
      TopsortHelper i' l' s' outgoing' incoming'
  | (S i', []) =>
      match EdgesFromAdjacencyList outgoing with
      | [] => (* No more edges in the graph - no cycle, total order found *)
          ReverseTotalOrder l
      | remaining_edges => (* Edges still remain in the graph - cycle found *)
          Cyclic remaining_edges
      end
  | (O, _) => Warning (Abort 0) ["Unexpected early termination!"]
  end.

(** *** [AdjacencyListTopsort] *)
(** Calculate the topological sort of an [AdjacencyList] *)
Definition AdjacencyListTopsort
  (a : AdjacencyList)
  : TopsortResult :=
  let e := EdgesFromAdjacencyList a in
  let n := NodesFromAdjacencyList a in
  let i := List.length n + List.length e + 1 in
  let s := SourceNodes e (Map (fst (A:=_) (B:=_)) a) in
  let a' := AdjacencyListFromEdges (Map ReverseEdge e) in
  TopsortHelper i [] s a a'.

(** *** [Topsort] *)
(** Calculate the topological sort of a list of [GraphEdge]s. *)
Definition Topsort
  (e : list GraphEdge)
  : TopsortResult :=
  let a := AdjacencyListFromEdges e in
  let n := NodesFromAdjacencyList a in
  let i := List.length n + List.length e + 1 in
  let s := SourceNodes e (Map (fst (A:=_) (B:=_)) a) in
  let a' := AdjacencyListFromEdges (Map ReverseEdge e) in
  TopsortHelper i [] s a a'.

Fixpoint TopsortGraphHelper
  (l : list GraphNode)
  (r : list GraphEdge)
  : list GraphEdge :=
  match l with
  | [] => r
  | h::t =>
      match t with
      | [] => r
      | t1::t2 => TopsortGraphHelper t ((t1, h, "", "black") :: r)
      end
  end.

Definition TopsortGraph
  (l : list GraphEdge)
  : list GraphEdge :=
  match Topsort l with
  | ReverseTotalOrder l' => TopsortGraphHelper l' []
  | _ => Warning [] ["Called TopsortGraph on cyclic graph!"]
  end.

(** ** Transitive Closure *)

Open Scope string_scope.

(** *** [TransitiveClosureHelper2] *)
(** Given a list [preds] of nodes [m] such that [(m, n)] is an edge in the
graph, add [succs] to the list of nodes reachable from [m], where [succs] is
the list of nodes reachable from [n]. *)
Fixpoint TransitiveClosureHelper2
  (a' tc : AdjacencyList)
  (preds : list (GraphNode * string * string))
  (succs : list GraphNode)
  : AdjacencyList :=
  match preds with
  | (h, _, _)::t =>
      let getLabel x :=
        match AdjacencyListFind a' x h with
        | Some label => label
        | None => ("TC", "gray")
        end in
      let f x :=
        let (label, color) := getLabel x in
        (h, x, label, color) in
      let edges := Map f succs in
      let tc' := fold_left AdjacencyListAddEdgeCheckDups edges tc in
      TransitiveClosureHelper2 a' tc' t succs
  | [] => tc
  end.

(** *** [TransitiveClosureHelper] *)
(** Add the list of nodes reachable from [n] to the list of nodes reachable
from each node with an edge going to [n] *)
Definition TransitiveClosureHelper
  (a' tc : AdjacencyList)
  (n : GraphNode)
  : AdjacencyList :=
  let preds := AdjacencyListGetDsts a' n in
  let f x := fst (fst x) in
  let succs := Map f (AdjacencyListGetDsts tc n) in
  TransitiveClosureHelper2 a' tc preds (n :: succs).

(** *** [TransitiveClosureResult] *)
(** Make it explicit when the algorithm failed. *)
Inductive TransitiveClosureResult : Set :=
| TC : AdjacencyList -> TransitiveClosureResult
| TCError : list GraphEdge -> TransitiveClosureResult.

(** *** [TransitiveClosure] *)
(** Calculate the transitive closure of a list of [GraphEdge]s. *)
Definition TransitiveClosure
  (l : list GraphEdge)
  : TransitiveClosureResult :=
  (* Inverse-adjacency list: the list of nodes [m] which have an edge going to
     [n].  Used to determine the predecessors of a node [n] *)
  let a' := AdjacencyListFromEdges (Map ReverseEdge l) in
  (* First do a [Topsort], then use that result to calculate the transitive
     closure *)
  match Topsort l with
  | ReverseTotalOrder l' => TC (fold_left (TransitiveClosureHelper a') l' [])
  | Cyclic e => TCError e (* FIXME: transitive closure of a cyclic graph *)
  | Abort _ => TCError [] (* FIXME: transitive closure of a cyclic graph *)
  end.

(** *** [AdjacencyListTransitiveClosure] *)
(** Calculate the transitive closure of an [AdjacencyList]. *)
Fixpoint AdjacencyListTransitiveClosure
  (a : AdjacencyList)
  : TransitiveClosureResult :=
  let e := EdgesFromAdjacencyList a in
  TransitiveClosure e.

(** ** Transitive Reduction *)
(** Drawing every edge in the transitive closure of the graph would be
extremely messy.  Instead, we can easily eliminate redundant edges along a
single "row" or "column" of the graph.*)

Definition IsTC
  (s : string)
  : bool :=
  beq_string "TC" s.

(** We don't actually want to remove *all* of the redundant edges; some of them
are actually better to keep in the graph for a better conceptual understanding.
For example: although (i1, store buffer) -> (i1, memory) -> (i2, store buffer)
may be true, it looks incomplete conceptually to not have the edge
(i1, store buffer) -> (i2, store buffer) in the graph. *)
Fixpoint TransitiveReductionCondition
  (a b c : GraphNode)
  (ab_label bc_label : string)
  (a_dst : GraphNode * string * string)
  : bool :=
  false.

(** *** [AdjacencyListTransitiveReduction] *)

(** Given [a], [b], and a list of [c] candidates, remove any (a --> c) edges
which (via [b]) are redundant, according to the condition
[TransitiveReductionCondition]. *)
Fixpoint AdjacencyListTransitiveReductionHelper3
  (a b : GraphNode)
  (ab_label : string)
  (b_ds : list (GraphNode * string * string))
  (a_ds' : list (GraphNode * string * string)) (* tail recursion result input *)
  : list (GraphNode * string * string) :=
  match b_ds with
  | (c, bc_label, bc_color)::t =>
      let a_ds'' :=
        let f x := andb (beq_node (fst (fst x)) c)
          (TransitiveReductionCondition a b c ab_label bc_label x) in
        removeb f a_ds' in
      AdjacencyListTransitiveReductionHelper3 a b ab_label t a_ds''
  | [] => a_ds'
  end.

(** Given [a] and a list of [b] candidates, find the list of [c] candidates. *)
Fixpoint AdjacencyListTransitiveReductionHelper2
  (g : AdjacencyList)
  (a : GraphNode)
  (a_ds : list (GraphNode * string * string))
  (a_ds' : list (GraphNode * string * string)) (* tail recursion result input *)
  : GraphNode * list (GraphNode * string * string) :=
  match a_ds with
  | (b, label, color)::t =>
      (* If a node is reachable from [h] and from [s], there is no need to
         draw the edge from [s], since it is redundant. *)
      let b_ds := AdjacencyListGetDsts g b in
      AdjacencyListTransitiveReductionHelper2 g a t
      (AdjacencyListTransitiveReductionHelper3 a b label b_ds a_ds')
  | [] => (a, a_ds')
  end.

(** Iterate through [g] to find the list of [a], [b] candidate pairs *)
Fixpoint AdjacencyListTransitiveReductionHelper
  (g : AdjacencyList)
  (g' : AdjacencyList) (* tail recursion result input *)
  : AdjacencyList :=
  match g' with
  | (a, ds)::t =>
      AdjacencyListTransitiveReductionHelper2 g a ds ds ::
      AdjacencyListTransitiveReductionHelper g t
  | [] => []
  end.

(** Calculate the transitive reduction of an adjacency list, but only delete
edges which satisfy the condition [TransitiveReductionCondition].  The goal is
to make the graph output cleaner but still informative, rather than to make the
graphs absolutely minimal. *)
Definition AdjacencyListTransitiveReduction
  (g : AdjacencyList)
  : AdjacencyList :=
  let f x := negb (IsTC (snd x)) in
  let g' := AdjacencyListFromEdges (AdjacencyListFilter f g) in
  AdjacencyListTransitiveReductionHelper g' g'.

(** ** Cycle Detection *)

(** One iteration of depth-first search: if the dst at the head of [dsts] is
[target], then we found the cycle: return it.  Otherwise, iterate one level
deeper.  If [dsts] is empty, then no cycle can be found from this point: back
up and try again with a different node. *)
Fixpoint CycleFromNodeHelper
  (g : AdjacencyList)
  (source target : GraphNode)
  (dsts : list (GraphNode * string * string))
  (l : list GraphEdge) (* tail recursion result input *)
  (i : nat) (* termination condition *)
  : option (list GraphEdge) :=
  match (i, dsts) with
  | (S i', (h, label, color)::t) =>
      if beq_node h target
      then (* Found the target and hence the cycle *)
        Some ((source, h, label, color) :: l)
      else (* Recurse one iteration deeper *)
        match CycleFromNodeHelper g h target (AdjacencyListGetDsts g h)
          ((source, h, label, color) :: l) i' with
        | Some l' => (* Found a cycle deeper; pass it along upwards *)
            Some l'
        | None => (* Didn't find a cycle; try again with the next dst node *)
            CycleFromNodeHelper g source target t l i'
        end
  | (S i', []) => (* Tried all of the dsts, but no cycle found *) None
  | _ => (* Error: reached the artificial termination condition *) None
  end.

(** *** [CycleFromNode] *)
(** Check whether there is a cycle in [l] including node [n].  If so, return
the edges in the cycle.  If not, return [None]. *)
Definition CycleFromNode
  (l : list GraphEdge)
  (n : GraphNode)
  : option (list GraphEdge) :=
  let g := AdjacencyListFromEdges l in 
  CycleFromNodeHelper g n n (AdjacencyListGetDsts g n) [] (List.length l).

(** Check whether there is a cycle from the node at the head of the list. *)
Fixpoint FindCycleHelper
  (l : list GraphEdge)
  (nodes : list GraphNode)
  : option (list GraphEdge) :=
  match nodes with
  | h::t =>
      match CycleFromNode l h with
      | Some l' => Some l'
      | None => FindCycleHelper l t
      end
  | [] => None
  end.

(** *** [FindCycle] *)
(** Find whether there is any cycle in [l].  If so, return the edges forming
the cycle. *)
Fixpoint FindCycle
  (l : list GraphEdge)
  : option (list GraphEdge) :=
  FindCycleHelper l (NodesFromEdges l).

(** ** [AdjacencyList], [Topsort], and [TransitiveClosure] Examples. *)

Module AdjacencyListExample.

Definition i0 := mkMicroop 0 0 0 0 (Write [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition i1 := mkMicroop 1 1 0 0 (Read  [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition i2 := mkMicroop 2 1 0 0 (Read  [] (VA 0 1) (PA (PTag 0) 1) (NormalData 0)).

Definition g := [
    ((i2, (1, 0)), (i0, (0, 2)), "a", "red");
    ((i0, (0, 2)), (i1, (1, 3)), "b", "red");
    ((i0, (0, 2)), (i1, (1, 4)), "c", "red")
  ].

Definition l := [
    ((i2, (1, 0)), [((i0, (0, 2)), "a", "red")]);
    ((i0, (0, 2)), [((i1, (1, 4)), "c", "red"); ((i1, (1, 3)), "b", "red")])
  ].

Example AdjacencyListExample1 :
  AdjacencyListFromEdges g = l.
Proof.
auto.
Qed.

Example AdjacencyListExample2 :
  AdjacencyListFind l (i2, (1, 0)) (i0, (0, 2)) = Some ("a", "red").
Proof.
auto.
Qed.

Example AdjacencyListExample3 :
  AdjacencyListFind l (i2, (1, 0)) (i0, (0, 4)) = None.
Proof.
auto.
Qed.

Definition n := [
    (i1, (1, 4)); (i1, (1, 3)); (i0, (0, 2)); (i2, (1, 0))
  ].

Example AdjacencyListExample4 :
  NodesFromEdges g = n.
Proof.
auto.
Qed.

Example AdjacencyListExample5 :
  TransitiveClosure g = TC [
    ((i2, (1, 0)),
      [((i1, (1, 4)), "TC", "gray"); ((i1, (1, 3)), "TC", "gray");
      ((i0, (0, 2)), "a", "red")]);
    ((i0, (0, 2)),
      [((i1, (1, 3)), "b", "red"); ((i1, (1, 4)), "c", "red")])
  ].
Proof.
auto.
Qed.

Example AdjacencyListExample6 :
  SourceNodes g (NodesFromEdges g) = [(i2, (1, 0))].
Proof.
auto.
Qed.

Example AdjacencyListExample7 :
  Topsort g = ReverseTotalOrder [
    (i1, (1, 4)); (i1, (1, 3)); (i0, (0, 2)); (i2, (1, 0))].
Proof.
auto.
Qed.

Example AdjacencyListExample8 :
  AdjacencyListTransitiveReduction
   [((i0, (0, 0)), [((i0, (0, 1)), "a", "red"); ((i0, (0, 2)), "b", "red")]);
    ((i0, (0, 1)), [((i0, (0, 2)), "c", "red")])] =
   [((i0, (0, 1)), [((i0, (0, 2)), "c", "red")]);
    ((i0, (0, 0)), [((i0, (0, 2)), "b", "red"); ((i0, (0, 1)), "a", "red")])].
Proof.
auto.
Qed.

Example AdjacencyListExample9 :
  CycleFromNode
    [((i0, (0, 0)), (i0, (0, 1)), "a", "red");
     ((i0, (0, 1)), (i0, (0, 2)), "b", "red");
     ((i0, (0, 2)), (i0, (0, 0)), "c", "red")]
    (i0, (0, 0))
  = Some
    [((i0, (0, 2)), (i0, (0, 0)), "c", "red");
     ((i0, (0, 1)), (i0, (0, 2)), "b", "red");
     ((i0, (0, 0)), (i0, (0, 1)), "a", "red")].
Proof.
auto.
Qed.

Example AdjacencyListExample10 :
  FindCycle
    [((i0, (0, 0)), (i0, (0, 1)), "a", "red");
     ((i0, (0, 1)), (i0, (0, 2)), "b", "red");
     ((i0, (0, 2)), (i0, (0, 0)), "c", "red")]
  = Some
    [((i0, (0, 1)), (i0, (0, 2)), "b", "red");
     ((i0, (0, 0)), (i0, (0, 1)), "a", "red");
     ((i0, (0, 2)), (i0, (0, 0)), "c", "red")].
Proof.
auto.
Qed.

Example AdjacencyListExample11 :
  FindCycle
    [((i0, (0, 0)), (i0, (0, 1)), "a", "red");
     ((i0, (0, 1)), (i0, (0, 2)), "b", "red");
     ((i0, (0, 2)), (i0, (0, 3)), "c", "red")]
  = None.
Proof.
auto.
Qed.

End AdjacencyListExample.

Fixpoint Zeros
  (n : nat)
  (s : string)
  : string :=
  match n with
  | S n' => Zeros n' (append s "0,")
  | 0 => s
  end.

Fixpoint StringOfNatListHelper
  (l : list nat)
  (min : nat)
  (s : string)
  : string :=
  match (min, l) with
  | (S min', h::t) =>
      StringOfNatListHelper t min' (StringOf [stringOfNat h; ","; s])
  | (0, h::t) =>
      StringOfNatListHelper t 0 (StringOf [stringOfNat h; ","; s])
  | (_, []) => Zeros min s
  end.

Definition StringOfNatList
  (l : list nat)
  (min : nat)
  : string :=
  StringOfNatListHelper (rev' l) min EmptyString.

Module StringOfNatListExamples.

Example e1 :
  StringOfNatList [1; 2; 3] 2 = "1,2,3,".
Proof.
  auto.
Qed.

Example e2 :
  StringOfNatList [1; 2; 3] 5 = "1,2,3,0,0,".
Proof.
  auto.
Qed.

End StringOfNatListExamples.

Definition ArchitectureLevelEdge := (nat * nat * string) % type.

