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
Require Import PipeGraph.Debug.
Require Import PipeGraph.Util.
Require Import PipeGraph.StringUtil.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Graph.

Import ListNotations.
Open Scope string_scope.

Definition GraphvizPrettyStringOfMicroop
  (uop : Microop)
  : string :=
  match uop with
  | mkMicroop g c t n a =>
      StringOf [
          "Inst ";
          if beq_nat 0 t then "" else StringOf ["t"; stringOfNat t; " "];
          stringOfNat g;
          if beq_nat 0 n then "" else StringOf [" i"; stringOfNat n];
          "\n";
          GraphvizStringOfMemoryAccess " " a;
          "\n"
      ]
  end.

(** ** [MicroopsFromNodes] *)
Fixpoint MicroopsFromNodesHelper
  (l : list GraphNode)
  (r : list Microop)
  : list Microop :=
  match l with
  | h::t =>
      match find (beq_uop (fst h)) r with
      | Some _ => MicroopsFromNodesHelper t r
      | None => MicroopsFromNodesHelper t ((fst h) :: r)
      end
  | [] => r
  end.

Definition MicroopsFromNodes
  (l : list GraphNode)
  : list Microop :=
  MicroopsFromNodesHelper l [].

Definition blt_uop
  (g : list GraphEdge)
  (a b : Microop)
  : bool :=
  let e1 := ((a, (coreID a, 0)), (b, (coreID b, 0)), "", "") in
  let e2 := ((b, (coreID b, 0)), (a, (coreID a, 0)), "", "") in
  if blt_nat (coreID a) (coreID b)
  then true
  else if blt_nat (coreID b) (coreID a)
  then false
  else if blt_nat (threadID a) (threadID b)
  then true
  else if blt_nat (threadID b) (threadID a)
  then false
  else if find (beq_edge e1) g
  then true
  else if find (beq_edge e2) g
  then false
  else if blt_nat (intraInstructionID a) (intraInstructionID b)
  then true
  else false.

Fixpoint SortMicroopsInsertionSortHelper
  (g : list GraphEdge)
  (l r : list Microop)
  (uop : Microop)
  : list Microop :=
  match l with
  | h::t =>
      if blt_uop g uop h
      then app_rev (uop::l) r
      else SortMicroopsInsertionSortHelper g t (h::r) uop
  | [] => app_rev [uop] r
  end.

Fixpoint AddDummyUarchEdgesForPOHelper
  (l : list ArchitectureLevelEdge)
  (uops : list Microop)
  (r : list GraphEdge)
  : list GraphEdge :=
  match l with
  | (a, b, c) :: t =>
      if beq_string "po" c
      then
        match (find (fun x => beq_nat (globalID x) a) uops,
          find (fun x => beq_nat (globalID x) b) uops) with
        | (Some a', Some b') =>
            let e := ((a', (coreID a', 0)), (b', (coreID b', 0)), c, "") in
            AddDummyUarchEdgesForPOHelper t uops (e::r)
        | (Some a', None) =>
            let result := (AddDummyUarchEdgesForPOHelper t uops r) in
            Warning result
              ["Could not find uop "; stringOfNat b; " while sorting graph!"]
        | (None, Some b') =>
            let result := (AddDummyUarchEdgesForPOHelper t uops r) in
            Warning result
              ["Could not find uop "; stringOfNat a; " while sorting graph!"]
        | (None, None) =>
            let result := (AddDummyUarchEdgesForPOHelper t uops r) in
            Warning result
              ["Could not find uops "; stringOfNat a; " or "; stringOfNat b;
               " while sorting graph!"]
        end
      else AddDummyUarchEdgesForPOHelper t uops r
  | [] => r
  end.

(** Transitive closure works on GraphEdges rather than ArchitectureLevelEdges,
 * so translate the ArchitectureLevelEdges into a form that TransitiveClosure
 * can work with *)
Definition AddDummyUarchEdgesForPO
  (l : list ArchitectureLevelEdge)
  (uops : list Microop)
  : list GraphEdge :=
  AddDummyUarchEdgesForPOHelper l uops [].

Definition SortMicroopsInsertionSort
  (g : list GraphEdge)
  (l : list Microop)
  (uop : Microop)
  : list Microop :=
  SortMicroopsInsertionSortHelper g l [] uop.

Definition SortMicroops
  (l : list Microop)
  (arch_edges : list ArchitectureLevelEdge)
  : list Microop :=
  let g := AddDummyUarchEdgesForPO arch_edges l in
  match TransitiveClosure g with
  | TC g' =>
      let g'' := EdgesFromAdjacencyList g' in
      fold_left (SortMicroopsInsertionSort g'') l []
  | TCError _ => Warning [] ["Cycle among program order edges?"]
  end.
Fixpoint MicroopXPositionsHelper
  (l : list Microop)
  (r : list (Microop * nat))
  (current : nat)
  (last_core : nat)
  : list (Microop * nat) :=
  match l with
  | h::t =>
      if beq_nat (coreID h) last_core
      then MicroopXPositionsHelper t ((h, current) :: r) (S current) last_core
      else MicroopXPositionsHelper t ((h, S current) :: r) (current + 2) (coreID h)
  | [] => r
  end.

Definition MicroopXPositions
  (l : list Microop)
  (arch_edges : list ArchitectureLevelEdge)
  : list (Microop * nat) :=
  MicroopXPositionsHelper (SortMicroops l arch_edges) [] 1 0.

Definition GraphvizNodeXPosition
  (l : list (Microop * nat))
  (uop : Microop)
  : string :=
  match find (fun x => beq_uop uop (fst x)) l with
  | Some (_, n) => stringOfNat n
  | None => Warning "-1" ["Could not calculate node X coordinate!"]
  end.

Definition GraphvizStringOfGraphNode
  (props : string)
  (xs : list (Microop * nat))
  (n : GraphNode)
  : string :=
  StringOf [tab; GraphvizShortStringOfGraphNode n; " [shape=circle;label=";
    quote; quote; ";"; "pos="; quote; GraphvizNodeXPosition xs (fst n); ",-";
    stringOfNat (snd (snd n)); "!"; quote; ";";
    props; "];";
    newline].

Definition GraphvizColorForEdgeLabel
  (c : string)
  : string :=
  StringOf ["color="""; c; """;fontcolor="""; c; """;"].

Definition GraphvizTextLabel
  (label : string)
  : string :=
  let f x := beq_string label x in
  let dont_label := ["PO"; "propagated"; "path"] in
  match find f dont_label with
  | Some z => EmptyString
  | None => StringOf ["label="; quote; label; quote; ";"]
  end.

Definition GraphvizStringOfGraphEdge
  (bold : list GraphEdge)
  (props : string)
  (e : GraphEdge)
  : string :=
  match e with
  | (s, d, label, color) =>
    let constraint :=
      if orb
        (beq_nat (globalID (fst s)) (globalID (fst d)))
        (andb
          (beq_nat 0 (snd (snd s)))
          (beq_nat 0 (snd (snd s))))
      then EmptyString
      else "constraint=false;"
    in
    let colorstring := GraphvizColorForEdgeLabel color in
    let thickness :=
      if existsb (beq_edge e) bold
      then "penwidth=5;"
      else EmptyString
    in
    let textlabel := GraphvizTextLabel label in
    StringOf [
      tab; GraphvizShortStringOfGraphNode s; " -> ";
      GraphvizShortStringOfGraphNode d; " ["; textlabel;
      constraint; colorstring; thickness; props; "];"; newline]
  end.

Definition GraphvizEdges
  (l : list GraphEdge)
  (bold : list GraphEdge)
  : list string :=
  Map (GraphvizStringOfGraphEdge bold "") l.

Fixpoint SetNthToMin
  (l : list (option nat))
  (p v : nat)
  : list (option nat) :=
  match (l, p) with
  | (Some h::t, 0   ) => Some (min h v) :: t
  | (Some h::t, S p') => Some h :: SetNthToMin t p' v
  | (None  ::t, 0   ) => Some v :: t
  | (None  ::t, S p') => None :: SetNthToMin t p' v
  | ([]       , 0   ) => [Some v]
  | ([]       , S p') => None :: SetNthToMin [] p' v
  end.

Module SetNthToMinExample.

Example e1: SetNthToMin [None; Some 2] 0 1 = [Some 1; Some 2].
Proof.
auto.
Qed.

Example e2: SetNthToMin [None; Some 2] 1 1 = [None; Some 1].
Proof.
auto.
Qed.

Example e3: SetNthToMin [None; Some 2] 1 3 = [None; Some 2].
Proof.
auto.
Qed.

End SetNthToMinExample.

Fixpoint GraphvizPipelineLabelXPositionHelper
  (l : list GraphNode)
  (xs : list (Microop * nat))
  (l' : list (option nat))
  : list (option nat) :=
  match l with
  | h::t =>
      match find (fun x => beq_uop (fst h) (fst x)) xs with
      | Some (_, n) =>
          GraphvizPipelineLabelXPositionHelper t xs
            (SetNthToMin l' (coreID (fst h)) (pred n))
      | None => GraphvizPipelineLabelXPositionHelper t xs l'
      end
  | [] => l'
  end.

Fixpoint GraphvizPipelineLabelXPositions
  (xs : list (Microop * nat))
  (l : list GraphNode)
  : list (option nat) :=
  GraphvizPipelineLabelXPositionHelper l xs [].

Fixpoint GraphvizLocationLabelStringsHelper2
  (x n : nat)
  (l l' : list string)
  : list string :=
  match l with
  | h::t =>
    GraphvizLocationLabelStringsHelper2 x (S n) t (
      StringOf [tab; "l"; stringOfNat x; "_"; stringOfNat n; "_label [label=";
        quote; h; quote; ";pos="; quote; stringOfNat x; ",-"; stringOfNat n;
        "!"; quote; ";shape=none];"; newline] :: l')
  | [] => l'
  end.

Fixpoint GraphvizLocationLabelStringsHelper
  (stage_names : list (list string))
  (label_x_positions : list (option nat))
  (l : list string)
  : list string :=
  match (stage_names, label_x_positions) with
  | (h1::t1, Some h2::t2) =>
      let l' := GraphvizLocationLabelStringsHelper2 h2 0 h1 [] in
      GraphvizLocationLabelStringsHelper t1 t2 (app_rev l l')
  | (h1::t1, None::t2) =>
      GraphvizLocationLabelStringsHelper t1 t2 l
  | _ => l
  end.

Definition GraphvizLocationLabels
  (stage_names : list (list string))
  (xs : list (Microop * nat))
  (l : list GraphNode)
  : list string :=
  let label_x_positions := GraphvizPipelineLabelXPositions xs l in
  GraphvizLocationLabelStringsHelper stage_names label_x_positions [].

Fixpoint GraphvizNodeLabelString
  (xs : list (Microop * nat))
  (uop : Microop)
  : string :=
  StringOf [tab; "n"; stringOfNat (globalID uop); "_";
    stringOfNat (intraInstructionID uop); "_label [label=";
    quote; GraphvizPrettyStringOfMicroop uop; quote; ";pos="; quote;
    GraphvizNodeXPosition xs uop; ",0.5!"; quote; ";shape=none];"; newline].

Fixpoint GraphvizNodeLabels
  (xs : list (Microop * nat))
  (l : list GraphNode)
  : list string :=
  Map (GraphvizNodeLabelString xs) (MicroopsFromNodes l).

Definition GraphvizNodes
  (stage_names : list (list string))
  (l : list GraphNode)
  (arch_edges : list ArchitectureLevelEdge)
  : list string :=
  let xs := MicroopXPositions (MicroopsFromNodes l) arch_edges in
  fold_left (app (A:=_)) [
    (Map (GraphvizStringOfGraphNode EmptyString xs) l);
    (GraphvizNodeLabels xs l);
    (GraphvizLocationLabels stage_names xs l)] [].

Definition IsNotTCEdge
  (e : GraphEdge)
  : bool :=
  match e with
  | (s, d, label, color) => negb (beq_string label "TC")
  end.

(** It is safe to pass an empty list as the [processor] and as the [pathmap] -
the names given in the graphviz output just won't be as helpful.  See above. *)
Definition GraphvizCompressedGraph
  (title : string)
  (stage_names : list (list string))
  (g : list GraphEdge)
  (* (do_reduction : bool) *)
  (thick_edges : list GraphEdge)
  (arch_edges : list ArchitectureLevelEdge)
  : list string :=
  let g' :=
    (* if do_reduction
    then *) filter IsNotTCEdge g
    (* else g *) in
  let bold_edges :=
    match thick_edges with
    | [] =>
      match Topsort g' with
      | Cyclic e =>
         match FindCycle e with
         | Some l => l
         | None => []
         end
      | _ => []
      end
    | _ => thick_edges
    end in
  fold_left (app (A:=_)) [
    ["digraph G {"; newline];
    [tab; "layout=neato;"; newline];
    [tab; "overlap=scale;"; newline];
    [tab; "splines=true;"; newline];
    [tab; "label="; quote; title; quote; ";"; newline];
    GraphvizEdges g' bold_edges;
    GraphvizNodes stage_names (NodesFromEdges g') arch_edges;
    ["}"; newline]
  ] [].

Module GraphvizExamples.

Example e1 :
  GraphvizShortStringOfGraphNode
    (mkMicroop 0 0 0 0 (Read [] (VA 1 0) (PA (PTag 1) 0) (NormalData 1)), (2, 3))
  = "n0_0_0_0_Read_y_1_at_2_3".
Proof.
  auto.
Qed.

Example e2 :
  GraphvizPrettyStringOfMicroop
    (mkMicroop 0 0 0 0 (Read [] (VA 1 0) (PA (PTag 1) 0) (NormalData 1)))
  = "Inst 0\nRead y 1\n".
Proof.
  auto.
Qed.

Example e3 :
  GraphvizStringOfGraphEdge
    []
    ""
    ((mkMicroop 0 0 0 0 (Write [] (VA 1 0) (PA (PTag 1) 0) (NormalData 1)), (2, 3)),
     (mkMicroop 1 0 0 0 (Read  [] (VA 1 0) (PA (PTag 1) 0) (NormalData 1)), (2, 3)),
     "myLabel", "red")
    = StringOf [tab; "n0_0_0_0_Write_y_1_at_2_3 -> n1_0_0_0_Read_y_1_at_2_3 [label="; quote; "myLabel"; quote; ";constraint=false;color=""red"";fontcolor=""red"";];"; newline].
Proof.
auto.
Qed.

Example e4 :
  GraphvizCompressedGraph "" []
    [((mkMicroop 0 0 0 0 (Write [] (VA 1 0) (PA (PTag 1) 0) (NormalData 1)), (2, 3)),
      (mkMicroop 1 0 0 0 (Read  [] (VA 1 0) (PA (PTag 1) 0) (NormalData 1)), (2, 3)),
      "myLabel", "red")] [] [(0, 1, "po")]
  = ["digraph G {"; newline;
    tab; "layout=neato;"; newline;
    tab; "overlap=scale;"; newline;
    tab; "splines=true;"; newline;
    tab; "label="; quote; EmptyString; quote; ";"; newline;
    StringOf [tab; "n0_0_0_0_Write_y_1_at_2_3 -> n1_0_0_0_Read_y_1_at_2_3 [label="; quote; "myLabel"; quote; ";constraint=false;color=""red"";fontcolor=""red"";];"; newline];
    StringOf [tab; "n1_0_0_0_Read_y_1_at_2_3 [shape=circle;label="""";pos="; quote; "2,-3!"; quote; ";];"; newline];
    StringOf [tab; "n0_0_0_0_Write_y_1_at_2_3 [shape=circle;label="""";pos="; quote; "1,-3!"; quote; ";];"; newline];
    StringOf [tab; "n0_0_label [label=""Inst 0\nWrite y 1\n"";pos=""1,0.5!"";shape=none];"; newline];
    StringOf [tab; "n1_0_label [label=""Inst 1\nRead y 1\n"";pos=""2,0.5!"";shape=none];"; newline];
    "}"; newline].
Proof.
auto.
Qed.

End GraphvizExamples.

Close Scope string_scope.
