Require Import Arith.
Require Import List.
Require Import String.
Require Import Ascii.
Require Import PipeGraph.Debug.
Require Import PipeGraph.Util.
Require Import PipeGraph.StringUtil.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Graph.
Require Import PipeGraph.FOLPredicate.
Require Import PipeGraph.GraphvizCompressed.

Open Scope string_scope.

Import ListNotations.

Definition beq_edge
  (a b : GraphEdge)
  : bool :=
  match (a, b) with
  | ((a1, a2, a3, a4), (b1, b2, b3, b4)) =>
      andb (beq_node a1 b1) (beq_node a2 b2)
  end.



Inductive ScenarioTree : Set :=
| ScenarioName : string -> ScenarioTree -> ScenarioTree
| ScenarioAnd : ScenarioTree -> ScenarioTree -> ScenarioTree
| ScenarioOr : ScenarioTree -> ScenarioTree -> ScenarioTree
| ScenarioEdgeLeaf : list GraphEdge -> ScenarioTree
| ScenarioNodeLeaf : list GraphNode -> ScenarioTree
| ScenarioNotNodeLeaf : list GraphNode -> ScenarioTree
| ScenarioTrue : ScenarioTree
| ScenarioFalse : ScenarioTree.

Fixpoint FlipEdgesHelper
  (l r : list GraphEdge)
  : list GraphEdge :=
  match l with
  | (s, d, label, c) :: t =>
      FlipEdgesHelper t ((d, s, label, c) :: r)
  | [] => r
  end.

Definition FlipEdges
  (l : list GraphEdge)
  : list GraphEdge :=
  FlipEdgesHelper l [].

Fixpoint PrintLabelsHelper
  (l : list string)
  (r : string)
  : string :=
  match l with
  | h::t => PrintLabelsHelper t (StringOf [h; "\n"; r])
  | [] => r
  end.

Definition PrintLabels
  (l : option (list string))
  : string :=
  match l with
  | Some l' => PrintLabelsHelper l' EmptyString
  | None => EmptyString
  end.

Definition PrintEdgeLabels
  (l : list GraphEdge)
  : string :=
  match l with
  | h::t =>
    fold_left (fun a b => StringOf [a; "\n"; ShortStringOfGraphEdge b]) t
      (ShortStringOfGraphEdge h)
  | [] => "-"
  end.

Definition PrintNodeLabels
  (l : list GraphNode)
  : string :=
  match l with
  | h::t =>
    fold_left (fun a b => StringOf [a; "\n"; ShortStringOfGraphNode b]) t
      (ShortStringOfGraphNode h)
  | [] => "-"
  end.

Fixpoint ScenarioTreeEdgeCountGraphHelper
  (ac : bool) (* all conjunctions *)
  (t : ScenarioTree)
  (id : nat)
  (n : option (list string))
  : nat * nat :=
  match t with
  | ScenarioName n'' t' =>
     match n with
     | Some n' => ScenarioTreeEdgeCountGraphHelper ac t' id (Some (n'' :: n'))
     | None => ScenarioTreeEdgeCountGraphHelper ac t' id (Some [n''])
     end
  | ScenarioEdgeLeaf l =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""";
        PrintLabels n;
        stringOfNat (List.length l); " edges\n";
        PrintEdgeLabels l; """];"]
  | ScenarioNodeLeaf l =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""";
        PrintLabels n;
        stringOfNat (List.length l); " nodes";
        PrintNodeLabels l; """];"]
  | ScenarioNotNodeLeaf l =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""";
        PrintLabels n;
        stringOfNat (List.length l); " nodes\nNot all of:\n";
        PrintNodeLabels l; """];"]
  | ScenarioAnd a b =>
      let (a_count, a_id) := ScenarioTreeEdgeCountGraphHelper ac a id None in
      let (b_count, b_id) := ScenarioTreeEdgeCountGraphHelper ac b (S a_id) None in
      let count := a_count * b_count in
      let color :=
        if andb (blt_nat 1 a_count) (blt_nat 1 b_count)
        then "green"
        else "black" in
      let result := (count, S b_id) in
      let result :=
        Println result ["  n"; stringOfNat (S b_id); " [shape=";
        if ac then "box" else "oval"; ",color=";
          color; ";label=""";
        PrintLabels n;
        "AND""];"] in
      let result := Println result ["  n"; stringOfNat (S b_id); " -> n";
        stringOfNat a_id; ";"] in
      let result := Println result ["  n"; stringOfNat (S b_id); " -> n";
        stringOfNat b_id; ";"] in
      result
  | ScenarioOr a b =>
      let (a_count, a_id) := ScenarioTreeEdgeCountGraphHelper false a id None in
      let (b_count, b_id) := ScenarioTreeEdgeCountGraphHelper false b (S a_id) None in
      let count := a_count + b_count in
      let color :=
        if andb (blt_nat 0 a_count) (blt_nat 0 b_count)
        then "blue"
        else "black" in
      let result := (count, S b_id) in
      let result :=
        Println result ["  n"; stringOfNat (S b_id); " [shape=";
        if ac then "box" else "oval"; ",color=blue;label=""";
        PrintLabels n;
        "OR""];"] in
      let result := Println result ["  n"; stringOfNat (S b_id); " -> n";
        stringOfNat a_id; ";"] in
      let result := Println result ["  n"; stringOfNat (S b_id); " -> n";
        stringOfNat b_id; ";"] in
      result
  | ScenarioTrue =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""TRUE""];"]
  | ScenarioFalse => 
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",color=red,label=""FALSE""];"]
  end.

Definition ScenarioTreeEdgeCountGraphHelper1
  (t : ScenarioTree)
  (n : string)
  : ScenarioTree :=
  let t := Println t ["digraph "; n; " {"] in
  let t := Println t [tab; "label="""; n; """;"] in
  let t := Println t [tab; "layout=dot;"] in
  let t := Println t [tab; "rankdir=LR;"] in
  let (count, _) := ScenarioTreeEdgeCountGraphHelper true t 0 None in
  Println t ["}"; newline; "// "; stringOfNat count; " scenarios"; newline].

Definition ScenarioTreeEdgeCountGraph
  (f : nat)
  (t : ScenarioTree)
  (n : string)
  : ScenarioTree :=
  if PrintFlag f
  then ScenarioTreeEdgeCountGraphHelper1 t n
  else t.

Fixpoint ReducesToTrue
  (t : ScenarioTree)
  : bool :=
  match t with
  | ScenarioName _ t' => ReducesToTrue t'
  | ScenarioEdgeLeaf [] => true
  | ScenarioEdgeLeaf _ => false
  | ScenarioNodeLeaf [] => true
  | ScenarioNodeLeaf _ => false
  | ScenarioNotNodeLeaf _ => false
  | ScenarioAnd a b => andb (ReducesToTrue a) (ReducesToTrue b)
  | ScenarioOr a b => orb (ReducesToTrue a) (ReducesToTrue b)
  | ScenarioTrue => true
  | ScenarioFalse => false
  end.

Fixpoint ReducesToFalse
  (t : ScenarioTree)
  : bool :=
  match t with
  | ScenarioName _ t' => ReducesToFalse t'
  | ScenarioEdgeLeaf _ => false
  | ScenarioNodeLeaf _ => false
  | ScenarioNotNodeLeaf [] => true
  | ScenarioNotNodeLeaf _ => false
  | ScenarioAnd a b => orb (ReducesToFalse a) (ReducesToFalse b)
  | ScenarioOr a b => andb (ReducesToFalse a) (ReducesToFalse b)
  | ScenarioTrue => false
  | ScenarioFalse => true
  end.

Fixpoint SimplifyScenarioTree
  (t : ScenarioTree)
  : ScenarioTree :=
  match t with
  | ScenarioName n t' =>
      match SimplifyScenarioTree t' with
      | ScenarioTrue => ScenarioTrue
      | ScenarioFalse => ScenarioFalse
      | t'' => ScenarioName n t''
      end
  | ScenarioEdgeLeaf [] => ScenarioTrue
  | ScenarioNodeLeaf [] => ScenarioTrue
  | ScenarioNotNodeLeaf [] => ScenarioFalse
  | ScenarioEdgeLeaf l => t
  | ScenarioNodeLeaf l => t
  | ScenarioNotNodeLeaf l => t
  | ScenarioAnd a b =>
      let a' := SimplifyScenarioTree a in
      let b' := SimplifyScenarioTree b in
      if ReducesToFalse a' then ScenarioFalse else
      if ReducesToFalse b' then ScenarioFalse else
      if ReducesToTrue a' then b' else
      if ReducesToTrue b' then a' else
      ScenarioAnd a' b'
  | ScenarioOr a b =>
      let a' := SimplifyScenarioTree a in
      let b' := SimplifyScenarioTree b in
      if ReducesToTrue a' then ScenarioTrue else
      if ReducesToTrue b' then ScenarioTrue else
      if ReducesToFalse a' then b' else
      if ReducesToFalse b' then a' else
      ScenarioOr a' b'
  | ScenarioTrue => t
  | ScenarioFalse => t
  end.

Fixpoint GuaranteedEdges
  (s : ScenarioTree)
  : (list GraphNode * list GraphNode * list GraphEdge) :=
  match s with
  | ScenarioName _ s => GuaranteedEdges s
  | ScenarioNodeLeaf l => (l, [], [])
  | ScenarioNotNodeLeaf l => ([], l, [])
  | ScenarioEdgeLeaf l => ([], [], l)
  | ScenarioAnd a b =>
      match (GuaranteedEdges a, GuaranteedEdges b) with
      | ((a1, a2, a3), (b1, b2, b3)) =>
          (app_rev a1 b1, app_rev a2 b2, app_rev a3 b3)
      end
  | ScenarioOr _ _ => ([], [], [])
  | ScenarioTrue => ([], [], [])
  | ScenarioFalse => Warning ([], [], [])
      ["Shouldn't try to calculate the GuaranteedEdges of FALSE"]
  end.

Fixpoint FindBranchingEdges
  (s : ScenarioTree)
  : option (list (list GraphEdge)) :=
  match s with
  | ScenarioName _ s => FindBranchingEdges s
  | ScenarioEdgeLeaf [] => None
  | ScenarioEdgeLeaf l => Some ([l])
  | ScenarioNodeLeaf l => Some []
  | ScenarioNotNodeLeaf l => Some []
  | ScenarioAnd a b =>
      match FindBranchingEdges a with
      | None => FindBranchingEdges b
      | Some [a1] =>
         match FindBranchingEdges b with
         | None => Some [a1]
         | Some [b1] => Some [app_rev a1 b1]
         | Some b' => Some b'
         end
      | Some a' => Some a'
      end
  | ScenarioOr a b =>
      match FindBranchingEdges a with
      | None => None
      | Some [l] =>
          match FindBranchingEdges b with
          | None => Some [l]
          | Some [l'] => Some [l; l']
          | Some l' => Some (l :: l')
          end
      | Some l =>
          match FindBranchingEdges b with
          | None => Some l
          | Some [l'] => Some (l' :: l)
          | Some l' => Some (app_rev l l')
          end
      end
  | ScenarioTrue => None
  | ScenarioFalse => None
  end.

Inductive FOLTerm : Set :=
| IntTerm : string -> nat -> FOLTerm
| StageNameTerm : string -> nat -> FOLTerm
| MicroopTerm : string -> Microop -> FOLTerm
| NodeTerm : string -> GraphNode -> FOLTerm
| EdgeTerm : string -> GraphEdge -> FOLTerm
| MacroArgTerm : string -> StringOrInt -> FOLTerm.

Definition FOLTermName
  (t : FOLTerm)
  : string :=
  match t with
  | IntTerm n _ => n
  | StageNameTerm n _ => n
  | MicroopTerm n _ => n
  | NodeTerm n _ => n
  | EdgeTerm n _ => n
  | MacroArgTerm n _ => n
  end.

Definition AddTerm
  (l : list FOLTerm)
  (t : FOLTerm)
  : list FOLTerm :=
  match find (fun x => beq_string (FOLTermName x) (FOLTermName t)) l with
  | Some _ => Warning (t::l) ["Shadowing term '"; FOLTermName t; "'"]
  | None => t::l
  end.

Definition stringOfFOLTermValue
  (t : FOLTerm)
  : string :=
  match t with
  | IntTerm _ n => stringOfNat n
  | StageNameTerm _ n => stringOfNat n
  | MicroopTerm _ uop => StringOf ["inst "; stringOfNat (globalID uop); " ";
      stringOfNat (coreID uop); " "; stringOfNat (threadID uop); " ";
      stringOfNat (intraInstructionID uop)]
  | NodeTerm _ n => GraphvizShortStringOfGraphNode n
  | EdgeTerm _ e => StringOfGraphEdge e
  | MacroArgTerm _ n => StringOfSoI n
  end.

Definition stringOfFOLTerm
  (t : FOLTerm)
  : string :=
  StringOf [FOLTermName t; " = ("; stringOfFOLTermValue t; ")"].

Fixpoint GetFOLTermHelper
  (name : string)
  (l : list FOLTerm)
  (depth : nat)
  : option FOLTerm :=
  match (depth, l) with
  | (S d, StageNameTerm s n::t) =>
      if beq_string s name
      then Some (IntTerm s n)
      else GetFOLTermHelper name t d
  | (S d, MacroArgTerm s1 s2::t) =>
      match s2 with
      | SoIString s2' =>
        if beq_string name s1
        then (if beq_string s1 s2'
          then GetFOLTermHelper name t d
          else GetFOLTermHelper s2' t d)
        else GetFOLTermHelper name t d
      | SoIInt n =>
        if beq_string s1 name
        then Some (IntTerm name n)
        else GetFOLTermHelper name t d
      | _ => Warning None ["Unexpected macro argument type"]
      end
  | (S d, h::t) =>
      if beq_string (FOLTermName h) name
      then Some h
      else GetFOLTermHelper name t d
  | (S d, []) => Warning None ["Could not find term "; name]
  | (O, _) => Warning None ["Term search recursion depth exceeded!"]
  end.

Definition GetFOLTerm
  (name : string)
  (l : list FOLTerm)
  : option FOLTerm :=
  let result := GetFOLTermHelper name l 1000 in
  match result with
  | Some r => if PrintFlag 8 then Comment result ["GetFOLTerm "; name; " returned "; stringOfFOLTerm r] else result
  | None => if PrintFlag 8 then Comment result ["GetFOLTerm "; name; " returned None"] else result
  end.

Record FOLState := mkFOLState {
  stateNodes     : list GraphNode;
  stateNotNodes  : list GraphNode;
  stateEdgeNodes : list GraphNode;
  stateEdges     : list GraphEdge;
  stateUops      : list Microop;
  stateInitial   : list BoundaryCondition;
  stateFinal     : list BoundaryCondition;
  stateArchEdges : list ArchitectureLevelEdge
}.

Definition UpdateFOLState
  (check_dups : bool)
  (s : FOLState)
  (l1 : list GraphEdge)
  : FOLState :=
  let f a b :=
    if find (beq_edge b) a
    then a
    else b::a
  in
  let new_edges :=
    if check_dups
    then fold_left f l1 (stateEdges s)
    else app_rev (stateEdges s) l1
  in
  let new_nodes := NodesFromEdges new_edges in
  mkFOLState (stateNodes s) (stateNotNodes s) new_nodes new_edges
    (stateUops s) (stateInitial s) (stateFinal s) (stateArchEdges s).

Fixpoint blt_string
  (a b : string)
  : bool :=
  match (a, b) with
  | (String a1 a2, String b1 b2) =>
      if blt_nat (nat_of_ascii a1) (nat_of_ascii b1)
      then true
      else if beq_nat (nat_of_ascii a1) (nat_of_ascii b1)
      then blt_string a2 b2
      else false
  | (String a1 a2, EmptyString) => false
  | (EmptyString, String b1 b2) => true
  | (EmptyString, EmptyString) => false
  end.

Definition FOLStateReplaceEdges
  (s : FOLState)
  (n n' : list GraphNode)
  (l : list GraphEdge)
  : FOLState :=
  let nodes := NodesFromEdges l in
  mkFOLState n n' nodes l (stateUops s) (stateInitial s)
    (stateFinal s) (stateArchEdges s).

Fixpoint GetSoIFOLTerm
  (t : StringOrInt)
  (l : list FOLTerm)
  : option FOLTerm :=
  let result :=
  match t with
  | SoISum a b =>
      match (GetSoIFOLTerm a l, GetSoIFOLTerm b l) with
      | (Some (IntTerm _ a'), Some (IntTerm _ b')) =>
          Some (IntTerm "" (a' + b'))
      | _ => None
      end
  | SoIString s => GetFOLTerm s l
  | SoIInt n => Some (IntTerm "" n)
  | SoICoreID s =>
      match GetFOLTerm s l with
      | Some (MicroopTerm _ uop) => Some (IntTerm "" (coreID uop))
      | _ => None
      end
  end in
  match result with
  | Some r => if PrintFlag 8 then Comment result ["GetSoIFOLTerm "; StringOfSoI t; " returned "; stringOfFOLTerm r] else result
  | None => if PrintFlag 8 then Comment result ["GetSoIFOLTerm "; StringOfSoI t; " returned None"] else result
  end.

Fixpoint FoldInstantiateGraphEdge
  (s : FOLState)
  (l : list FOLTerm)
  (r : option (list GraphEdge))
  (e : PredGraphEdge)
  : option (list GraphEdge) :=
  match e with
  | ((uop1name, (p1, l1)), (uop2name, (p2, l2)), label, color) =>
      match (GetFOLTerm uop1name l, GetFOLTerm uop2name l,
             GetSoIFOLTerm p1 l, GetSoIFOLTerm p2 l,
             GetSoIFOLTerm l1 l, GetSoIFOLTerm l2 l) with
      | (Some (MicroopTerm _ uop1), Some (MicroopTerm _ uop2),
         Some (IntTerm _ p1'), Some (IntTerm _ p2'),
         Some (IntTerm _ l1'), Some (IntTerm _ l2')) =>
          let e  := ((uop1, (p1', l1')), (uop2, (p2', l2')), label, color) in
          match r with
          | Some r' => Some (e :: r')
          | None => None
          end
      | _ => Warning None ["Could not find microop terms "; uop1name;
          " and/or "; uop2name]
      end
  end.

Fixpoint FoldInstantiateGraphNode
  (s : FOLState)
  (l : list FOLTerm)
  (r : option (list GraphNode))
  (n : PredGraphNode)
  : option (list GraphNode) :=
  match n with
  | (uopname, (p1, l1)) =>
      match (GetFOLTerm uopname l, GetSoIFOLTerm p1 l, GetSoIFOLTerm l1 l) with
      | (Some (MicroopTerm _ uop), Some (IntTerm _ p'), Some (IntTerm _ l')) =>
          let n := (uop, (p', l')) in
          match r with
          | Some r' => Some (n :: r')
          | None => None
          end
      | _ => Warning None ["Could not find term "; uopname]
      end
  end.

Fixpoint GetInitialCondition
  (conditions : list BoundaryCondition)
  (pa : PhysicalAddress)
  : Data :=
  match conditions with
  | (a, d) :: t =>
      if beq_paddr a pa
      then d
      else GetInitialCondition t pa
  | [] =>
      let result := NormalData 0 in
      if PrintFlag 6
      then Comment result
        ["Using implicit initial condition data=0 for PA: ";
        GraphvizStringOfPhysicalAddress pa]
      else result
  end.

Fixpoint GetFinalCondition
  (conditions : list BoundaryCondition)
  (pa : PhysicalAddress)
  : option Data :=
  match conditions with
  | (a, d) :: t =>
      if beq_paddr a pa
      then Some d
      else GetFinalCondition t pa
  | [] => None
  end.

Fixpoint HasDependency
  (l : list ArchitectureLevelEdge)
  (src dst : nat)
  (label : string)
  : bool :=
  match l with
  | (h1, h2, h3)::t =>
      if andb (andb (beq_nat h1 src) (beq_nat h2 dst))
        (beq_string label h3)
      then true
      else HasDependency t src dst label
  | [] => false
  end.

Definition EvaluatePredicate
  (stage_names : list (list string))
  (p : FOLPredicateType)
  (l : list FOLTerm)
  (s : FOLState)
  : option (list GraphNode * list GraphEdge) :=
  let result := match p with
  | PredDebug a => Some ([], [])
  | PredHasDependency a b c =>
      match (GetFOLTerm b l, GetFOLTerm c l) with
      | (Some (MicroopTerm _ b'), Some (MicroopTerm _ c')) =>
          if HasDependency (stateArchEdges s) (globalID b') (globalID c') a
          then Some ([], [])
          else None
      | _ => None
      end
  | PredIsRead t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match access t' with
          | Read _ _ _ _ => Some ([], [])
          | _ => None
          end
      | _ => None
      end
  | PredIsAPICAccess n t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match access t' with
          | Read _ _ (PA (APICTag s' _) _) _ =>
              if beq_string n s' then Some ([], []) else None
          | Write _ _ (PA (APICTag s' _) _) _ =>
              if beq_string n s' then Some ([], []) else None
          | _ => None
          end
      | _ => None
      end
  | PredIsWrite t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match access t' with
          | Write _ _ _ _ => Some ([], [])
          | _ => None
          end
      | _ => None
      end
  | PredIsFence t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match access t' with
          | Fence _ => Some ([], [])
          | FenceVA _ _ => Some ([], [])
          | _ => None
          end
      | _ => None
      end
  | PredAccessType t1 t2 =>
      match GetFOLTerm t2 l with
      | Some (MicroopTerm _ t2') =>
          match access t2' with
          | Read t1' _ _ _ =>
              if find_string t1 t1'
              then Some ([], [])
              else None
          | Write t1' _ _ _ =>
              if find_string t1 t1'
              then Some ([], [])
              else None
          | Fence t1' =>
              if find_string t1 t1'
              then Some ([], [])
              else None
          | FenceVA t1' _ =>
              if find_string t1 t1'
              then Some ([], [])
              else None
          end
      | _ => None
      end
  | PredSameUop t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_uop t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSameCore t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetSoIFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat (coreID t1') (coreID t2')
          then Some ([], [])
          else None
      | (Some (IntTerm _ t1'), Some (IntTerm _ t2')) =>
          if beq_nat t1' t2'
          then Some ([], [])
          else None
      | _ => None
      end
  | PredOnCore t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (IntTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat t1' (coreID t2')
          then Some ([], [])
          else None
      | _ => Warning None ["Could not find term "; StringOfSoI t1; " and/or "; t2]
      end
  | PredSameThread t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetSoIFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat (coreID t1') (coreID t2')
          then Some ([], [])
          else None
      | (Some (IntTerm _ t1'), Some (IntTerm _ t2')) =>
          if beq_nat t1' t2'
          then Some ([], [])
          else None
      | _ => None
      end
  | PredSmallerGlobalID t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if blt_nat (globalID t1') (globalID t2')
          then Some ([], [])
          else None
      | _ => None
      end
  | PredSameGlobalID t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat (globalID t1') (globalID t2')
          then Some ([], [])
          else None
      | _ => None
      end
  | PredSameIntraInstID t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat (intraInstructionID t1') (intraInstructionID t2')
          then Some ([], [])
          else None
      | _ => None
      end
  | PredOnThread t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (IntTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat t1' (threadID t2')
          then Some ([], [])
          else None
      | _ => Warning None ["Could not find term "; StringOfSoI t1; " and/or "; t2]
      end
  | PredSameNode t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (NodeTerm _ t1'), Some (NodeTerm _ t2')) =>
          if beq_node t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSameVirtualAddress t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SameVirtualAddress t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSamePhysicalAddress t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SamePhysicalAddress t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSameVirtualTag t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SameVirtualTag t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSamePhysicalTag t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SamePhysicalTag t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSameIndex t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SameIndex t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredKnownData t1 =>
      match (GetFOLTerm t1 l) with
      | Some (MicroopTerm _ t1') =>
          match access t1' with
          | Read _ _ _ UnknownData => None
          | _ => Some ([], [])
          end
      | _ => None
      end
  | PredSameData t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SameData t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSamePAasPTEforVA t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          match (GetPhysicalAddress t1', GetVirtualTag t2') with
          | (Some p1, Some v2) =>
              if beq_paddr p1 (PA (PTETag v2) 0)
              then Some ([], [])
              else None
          | _ => None
          end
      | _ => None
      end
  | PredDataIsCorrectTranslation a' d' t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          match (GetData t1', GetVirtualTag t2', GetPhysicalTag t2') with
          | (Some d, Some v, Some p) =>
              if beq_pte d v p a' d'
              then Some ([], [])
              else None
          | _ => None
          end
      | _ => None
      end
  | PredTranslationMatchesInitialState a' d' t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match (GetVirtualTag t', GetPhysicalTag t') with
          | (Some v, Some p) =>
              let ic :=
                GetInitialCondition (stateInitial s) (PA (PTETag v) 0) in
              if beq_pte ic v p a' d'
              then Some ([], [])
              else None
          | _ => None
          end
      | _ => None
      end
  | PredDataFromPAInitial t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match (GetData t', GetPhysicalAddress t') with
          | (Some d, Some pa) =>
              if beq_data d (GetInitialCondition (stateInitial s) pa)
              then Some ([], [])
              else None
          | _ => None
          end
      | _ => None
      end
  | PredDataFromPAFinal t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match (GetData t', GetPhysicalAddress t') with
          | (Some d, Some pa) =>
              match GetFinalCondition (stateFinal s) pa with
              | Some d' =>
                if beq_data d d'
                then Some ([], [])
                else None
              | None => None
              end
          | _ => None
          end
      | _ => None
      end
  | PredConsec t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if andb (beq_nat (S (globalID t1')) (globalID t2'))
            (andb (beq_nat (threadID t1') (threadID t2'))
              (beq_nat (coreID t1') (coreID t2')))
          then Some ([], [])
          else None
      | _ => None
      end
  | PredProgramOrder t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ b'), Some (MicroopTerm _ c')) =>
          if HasDependency (stateArchEdges s) (globalID b') (globalID c') "po"
          then Some ([], [])
          else None
      | _ => None
      end
  | PredAddEdges e
  | PredEdgesExist e =>
      match fold_left (FoldInstantiateGraphEdge s l) e (Some []) with
      | Some l' => Some ([], l')
      | None => None
      end
  | PredNodesExist n =>
      match fold_left (FoldInstantiateGraphNode s l) n (Some []) with
      | Some l' => Some (l', [])
      | None => None
      end
  | PredTrue => Some ([], [])
  | PredFalse => None
  | PredHasID g c t i n =>
      match GetFOLTerm n l with
      | Some (MicroopTerm _ uop) =>
          match uop with
          | mkMicroop g' c' t' i' _ =>
              if andb
                (andb (beq_nat g g') (beq_nat c c'))
                (andb (beq_nat t t') (beq_nat i i'))
              then Some ([], [])
              else None
          end
      | _ => None
      end
  | PredHasGlobalID g n =>
      match GetFOLTerm n l with
      | Some (MicroopTerm _ uop) =>
          match uop with
          | mkMicroop g' _ _ _ _ =>
              if beq_nat g g'
              then Some ([], [])
              else None
          end
      | _ => None
      end
  end in
  if PrintFlag 8
  then Comment result [tab; "// EvaluatePredicate "; stringOfPredicate false p; " returned ";
    match result with
    | Some (l1, l2) => StringOf ["sat("; stringOfNat (List.length l1); " nodes, ";
        stringOfNat (List.length l2); " edges)"]
    | None => "unsat"
    end]
  else result.

Definition FOLQuantifier := FOLState -> list FOLTerm -> (string * list FOLTerm).

Definition MicroopQuantifier
  (name : string)
  : FOLQuantifier :=
  fun (s : FOLState) (l : list FOLTerm) =>
  let uops := stateUops s in
  (name, Map (fun x => MicroopTerm name x) uops).

Definition NodeQuantifier
  (name : string)
  : FOLQuantifier :=
  fun (s : FOLState) (l : list FOLTerm) =>
  let nodes := stateNodes s in
  (name, Map (fun x => NodeTerm name x) nodes).

Fixpoint numCores
  (l : list Microop)
  (n : nat)
  : nat :=
  match l with
  | h::t => numCores t (max n (S (coreID h)))
  | [] => n
  end.

Definition CoreQuantifier
  (name : string)
  : FOLQuantifier :=
  fun (s : FOLState) (l : list FOLTerm) =>
  let cores := numCores (stateUops s) 0 in
  (name, Map (fun x => IntTerm name x) (Range cores)).

Fixpoint numThreads
  (l : list Microop)
  (n : nat)
  : nat :=
  match l with
  | h::t => numThreads t (max n (S (threadID h)))
  | [] => n
  end.

Definition ThreadQuantifier
  (name : string)
  : FOLQuantifier :=
  fun (s : FOLState) (l : list FOLTerm) =>
  let cores := numThreads (stateUops s) 0 in
  (name, Map (fun x => IntTerm name x) (Range cores)).

Inductive FOLFormula :=
| FOLName : string -> FOLFormula -> FOLFormula
| FOLExpandMacro : string -> list StringOrInt -> FOLFormula
| FOLPredicate : FOLPredicateType -> FOLFormula
| FOLNot : FOLFormula -> FOLFormula
| FOLOr : FOLFormula -> FOLFormula -> FOLFormula
| FOLAnd : FOLFormula -> FOLFormula -> FOLFormula
| FOLForAll : FOLQuantifier -> FOLFormula -> FOLFormula
| FOLExists : FOLQuantifier -> FOLFormula -> FOLFormula
| FOLLet : FOLTerm -> FOLFormula -> FOLFormula.

Fixpoint stringOfFOLFormulaHelper
  (n : nat)
  (depth : nat)
  (f : FOLFormula)
  : string :=
  match n with
  | S n' =>
      match f with
      | FOLName s f => StringOf ["("; s; ":(";
          stringOfFOLFormulaHelper n' (S depth) f; "))"]
      | FOLExpandMacro s l => StringOf ["ExpandMacro "; s]
      | FOLPredicate p => stringOfPredicate false p
      | FOLNot f' => StringOf ["~("; stringOfNat depth; ")(";
          stringOfFOLFormulaHelper n' (S depth) f'; ")"]
      | FOLOr a b =>
          StringOf ["("; stringOfFOLFormulaHelper n' (S depth) a; ") \";
            stringOfNat depth ; "/ (";
            stringOfFOLFormulaHelper n' (S depth) b; ")"]
      | FOLAnd a b =>
          StringOf ["("; stringOfFOLFormulaHelper n' (S depth) a; ") /";
            stringOfNat depth; "\ (";
            stringOfFOLFormulaHelper n' (S depth) b; ")"]
      | FOLForAll q f' =>
          StringOf ["forall("; stringOfNat depth; ") (...), (";
            stringOfFOLFormulaHelper n' (S depth) f'; ")"]
      | FOLExists q f' =>
          StringOf ["exists("; stringOfNat depth; ") (...), (";
            stringOfFOLFormulaHelper n' (S depth) f'; ")"]
      | FOLLet t f' =>
          StringOf ["let("; stringOfNat depth; ") "; stringOfFOLTerm t;
            " in ("; stringOfFOLFormulaHelper n' (S depth) f'; ")"]
      end
  | O =>
      match f with
      | FOLName s f' => s
      | FOLExpandMacro s l => StringOf ["ExpandMacro "; s]
      | FOLPredicate p => stringOfPredicate false p
      | FOLNot f' => "~(...)"
      | FOLOr a b => "(...) \/ (...)"
      | FOLAnd a b => "(...) /\ (...)"
      | FOLForAll q f' => "forall (...), (...)"
      | FOLExists q f' => "exists (...), (...)"
      | FOLLet t f' => StringOf ["let "; stringOfFOLTerm t; " in (...)"]
      end
  end.

Definition stringOfFOLFormula
  (depth : nat)
  (f : FOLFormula)
  : string :=
  stringOfFOLFormulaHelper 3 depth f.

Fixpoint PrintGraphvizStringOfFOLFormulaHelper
  (id : nat)
  (f : FOLFormula)
  : nat :=
  match f with
  | FOLName s f' =>
      let id' := PrintGraphvizStringOfFOLFormulaHelper id f' in
      let result := S id' in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat id'; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [color=red,shape=box,label="""; s; """];"] in
      result
  | FOLExpandMacro s l =>
      Println id ["  n"; stringOfNat id; " [label="""; s; """];"]
  | FOLPredicate p =>
      Println id
        ["  n"; stringOfNat id; " [label="""; stringOfPredicate true p; """];"]
  | FOLNot f' =>
      let id' := PrintGraphvizStringOfFOLFormulaHelper id f' in
      let result := S id' in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat id'; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [label=""NOT""];"] in
      result
  | FOLOr a b =>
      let a_id := PrintGraphvizStringOfFOLFormulaHelper      id  a in
      let b_id := PrintGraphvizStringOfFOLFormulaHelper (S a_id) b in
      let result := S b_id in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat a_id; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat b_id; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [label=""OR""];"] in
      result
  | FOLAnd a b =>
      let a_id := PrintGraphvizStringOfFOLFormulaHelper      id  a in
      let b_id := PrintGraphvizStringOfFOLFormulaHelper (S a_id) b in
      let result := S b_id in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat a_id; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat b_id; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [label=""AND""];"] in
      result
  | FOLForAll q f' =>
      let id' := PrintGraphvizStringOfFOLFormulaHelper id f' in
      let result := S id' in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat id'; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [label=""forall ...""];"] in
      result
  | FOLExists q f' =>
      let id' := PrintGraphvizStringOfFOLFormulaHelper id f' in
      let result := S id' in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat id'; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [label=""exists ...""];"] in
      result
  | FOLLet t f' =>
      let id' := PrintGraphvizStringOfFOLFormulaHelper id f' in
      let result := S id' in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat id'; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [color=green,shape=box,label="""; stringOfFOLTerm t; """];"] in
      result
  end.

Definition PrintGraphvizStringOfFOLFormula
  (f : FOLFormula)
  : FOLFormula :=
  if PrintFlag 5
  then
    let f := Println f ["digraph Axioms {"] in
    let f := Println f [tab; "layout=dot;"] in
    let result := PrintGraphvizStringOfFOLFormulaHelper 0 f in
    Println f ["} // "; stringOfNat result; " nodes"; newline]
  else f.

Definition FOLImplies
  (a b : FOLFormula)
  : FOLFormula :=
  FOLOr (FOLNot a) b.

Definition FOLIff
  (a b : FOLFormula)
  : FOLFormula :=
  FOLAnd (FOLImplies a b) (FOLImplies b a).

Definition FoldFlipEdge
  (t : ScenarioTree)
  (e : GraphEdge)
  : ScenarioTree :=
  match e with
  | (s, d, l, c) =>
      let l' :=
        if string_prefix "NOT_" l
        then substr 4 l
        else append "NOT_" l in
      if beq_node s d
      then ScenarioOr t ScenarioTrue
      else ScenarioOr t
        (ScenarioOr
          (ScenarioOr (ScenarioNotNodeLeaf [s]) (ScenarioNotNodeLeaf [d]))
          (ScenarioEdgeLeaf [(d, s, l', c)]))
  end.

Definition FoldFlipNode
  (t : ScenarioTree)
  (n : GraphNode)
  : ScenarioTree :=
  ScenarioOr t (ScenarioNotNodeLeaf [n]).

Fixpoint EliminateQuantifiersHelper
  (demorgan : bool)
  (stage_names : list (list string))
  (s : FOLState)
  (f : FOLFormula)
  (l : list FOLTerm)
  : ScenarioTree :=
  match f with
  | FOLName n f =>
      ScenarioName n (EliminateQuantifiersHelper demorgan stage_names s f l)
  | FOLExpandMacro m _ => Warning ScenarioFalse
      ["Internal error: macro "; m; " should have been expanded!"]
  | FOLPredicate p  =>
      match (demorgan, EvaluatePredicate stage_names p l s) with
      | (false, Some (l1, l2)) =>
          ScenarioAnd (ScenarioNodeLeaf l1) (ScenarioEdgeLeaf l2)
      | (false, None) => ScenarioFalse
      | (true, Some (l1, l2)) =>
          let n := fold_left FoldFlipNode l1 ScenarioFalse in
          let e := fold_left FoldFlipEdge l2 ScenarioFalse in
          ScenarioOr n e
      | (true, None) => ScenarioTrue
      end
  | FOLNot f' =>
      EliminateQuantifiersHelper (negb demorgan) stage_names s f' l
  | FOLOr a b =>
      if demorgan
      then
        match (EliminateQuantifiersHelper demorgan stage_names s a l) with
        | ScenarioFalse => ScenarioFalse
        | ScenarioTrue =>
          (EliminateQuantifiersHelper demorgan stage_names s b l)
        | a' =>
          match (EliminateQuantifiersHelper demorgan stage_names s b l) with
          | ScenarioFalse => ScenarioFalse
          | ScenarioTrue => a'
          | b' => ScenarioAnd a' b'
          end
        end
      else
        match (EliminateQuantifiersHelper demorgan stage_names s a l) with
        | ScenarioTrue => ScenarioTrue
        | ScenarioFalse =>
          (EliminateQuantifiersHelper demorgan stage_names s b l)
        | a' =>
          match (EliminateQuantifiersHelper demorgan stage_names s b l) with
          | ScenarioTrue => ScenarioTrue
          | ScenarioFalse => a'
          | b' => ScenarioOr a' b'
          end
        end
  | FOLAnd a b =>
      if negb demorgan
      then
        match (EliminateQuantifiersHelper demorgan stage_names s a l) with
        | ScenarioFalse => ScenarioFalse
        | ScenarioTrue =>
          (EliminateQuantifiersHelper demorgan stage_names s b l)
        | a' =>
          match (EliminateQuantifiersHelper demorgan stage_names s b l) with
          | ScenarioFalse => ScenarioFalse
          | ScenarioTrue => a'
          | b' => ScenarioAnd a' b'
          end
        end
      else
        match (EliminateQuantifiersHelper demorgan stage_names s a l) with
        | ScenarioTrue => ScenarioTrue
        | ScenarioFalse =>
          (EliminateQuantifiersHelper demorgan stage_names s b l)
        | a' =>
          match (EliminateQuantifiersHelper demorgan stage_names s b l) with
          | ScenarioTrue => ScenarioTrue
          | ScenarioFalse => a'
          | b' => ScenarioOr a' b'
          end
        end
  | FOLForAll t f'  =>
      let (term_name, terms) := t s l in
      let case x y :=
        if demorgan
        then
          match x with
          | ScenarioTrue => ScenarioTrue
          | ScenarioFalse =>
            let y' := EliminateQuantifiersHelper demorgan stage_names s f' (AddTerm l y) in
            ScenarioName (stringOfFOLTerm y) y'
          | _ =>
            match EliminateQuantifiersHelper demorgan stage_names s f' (AddTerm l y) with
            | ScenarioTrue => ScenarioTrue
            | ScenarioFalse => x
            | y' => ScenarioOr x (ScenarioName (stringOfFOLTerm y) y')
            end
          end
        else
          match x with
          | ScenarioFalse => ScenarioFalse
          | ScenarioTrue =>
            let y' := EliminateQuantifiersHelper demorgan stage_names s f' (AddTerm l y) in
            ScenarioName (stringOfFOLTerm y) y'
          | _ =>
            match EliminateQuantifiersHelper demorgan stage_names s f' (AddTerm l y) with
            | ScenarioFalse => ScenarioFalse
            | ScenarioTrue => x
            | y' => ScenarioAnd x (ScenarioName (stringOfFOLTerm y) y')
            end
          end in
      fold_left case terms (if demorgan then ScenarioFalse else ScenarioTrue)
  | FOLExists t f'  =>
      let (term_name, terms) := t s l in
      let case x y :=
        if negb demorgan
        then
          match x with
          | ScenarioTrue => ScenarioTrue
          | ScenarioFalse =>
            let y' := EliminateQuantifiersHelper demorgan stage_names s f' (AddTerm l y) in
            ScenarioName (stringOfFOLTerm y) y'
          | _ =>
            match EliminateQuantifiersHelper demorgan stage_names s f' (AddTerm l y) with
            | ScenarioTrue => ScenarioTrue
            | ScenarioFalse => x
            | y' => ScenarioOr x (ScenarioName (stringOfFOLTerm y) y')
            end
          end
        else
          match x with
          | ScenarioFalse => ScenarioFalse
          | ScenarioTrue =>
            let y' := EliminateQuantifiersHelper demorgan stage_names s f' (AddTerm l y) in
            ScenarioName (stringOfFOLTerm y) y'
          | _ =>
            match EliminateQuantifiersHelper demorgan stage_names s f' (AddTerm l y) with
            | ScenarioFalse => ScenarioFalse
            | ScenarioTrue => x
            | y' => ScenarioAnd x (ScenarioName (stringOfFOLTerm y) y')
            end
          end in
      fold_left case terms (if demorgan then ScenarioTrue else ScenarioFalse)
  | FOLLet t f' =>
      let t' := EliminateQuantifiersHelper demorgan stage_names s f' (AddTerm l t) in
      ScenarioName (stringOfFOLTerm t) t'
  end.

Fixpoint SetIntersectionIsEmpty
  (a b : list GraphEdge)
  : bool :=
  match a with
  | h::t =>
      if find (beq_edge h) b
      then false
      else SetIntersectionIsEmpty t b
  | [] => true
  end.

Fixpoint SetIntersectionHelper
  (a b : list GraphEdge)
  (r : list GraphEdge)
  : list GraphEdge :=
  match a with
  | h::t =>
      if find (beq_edge h) b
      then SetIntersectionHelper t b (h::r)
      else SetIntersectionHelper t b r
  | [] => r
  end.

Definition SetIntersection
  (a b : list GraphEdge)
  : list GraphEdge :=
  SetIntersectionHelper a b [].

(** If a match is found, then pick which to keep according to the following
list of priorities:
1) Labeled edges
2) TC
3) Flipped edges
*)
Fixpoint SDFindEdge
  (e : GraphEdge)
  (l : list GraphEdge)
  : option GraphEdge :=
  match l with
  | h::t =>
      if beq_edge h e
      then
        match (h, e) with
        | ((hs, hd, hl, hc), (es, ed, el, ec)) =>
          match (beq_string "TC" hl, string_prefix "NOT_" hl,
            beq_string "TC" el, string_prefix "NOT_" el) with
          | (true, true, _, _) => Warning None
              ["TC and NOT_ simultaneously?"]
          | (_, _, true, true) => Warning None
              ["TC and NOT_ simultaneously?"]
          | (false, false, _, _) => None
          | (true, _, false, false) => Some e
          | (true, _, _, _) => None
          | (_, true, false, true) => None
          | (_, true, _, false) => Some e
          end
        end
      else SDFindEdge e t
  | [] => Some e
  end.

Fixpoint SetDifferenceHelper
  (a b r : list GraphEdge)
  : list GraphEdge :=
  match a with
  | h::t =>
      match SDFindEdge h b with
      | Some e => SetDifferenceHelper t b (e::r)
      | None => SetDifferenceHelper t b r
      end
  | [] => r
  end.

Definition SetDifference
  (a b : list GraphEdge)
  : list GraphEdge :=
  SetDifferenceHelper a b [].

Fixpoint NodeSetIntersectionIsEmpty
  (a b : list GraphNode)
  : bool :=
  match a with
  | h::t =>
      if find (beq_node h) b
      then false
      else NodeSetIntersectionIsEmpty t b
  | [] => true
  end.

Fixpoint NodeSetIntersectionHelper
  (a b : list GraphNode)
  (r : list GraphNode)
  : list GraphNode :=
  match a with
  | h::t =>
      if find (beq_node h) b
      then NodeSetIntersectionHelper t b (h::r)
      else NodeSetIntersectionHelper t b r
  | [] => r
  end.

Fixpoint NodeSetIntersection
  (a b : list GraphNode)
  : list GraphNode :=
  NodeSetIntersectionHelper a b [].

Fixpoint NodeSetDifferenceHelper
  (a b r : list GraphNode)
  : list GraphNode :=
  match a with
  | h::t =>
      if find (beq_node h) b
      then NodeSetDifferenceHelper t b r
      else NodeSetDifferenceHelper t b (h::r)
  | [] => r
  end.

Definition NodeSetDifference
  (a b : list GraphNode)
  : list GraphNode :=
  NodeSetDifferenceHelper a b [].

Fixpoint ScenarioTreeKeepIfFalse
  (s : FOLState)
  (t : ScenarioTree)
  : option ScenarioTree :=
  match t with
  | ScenarioName n t' =>
      match ScenarioTreeKeepIfFalse s t' with
      | Some t'' => Some (ScenarioName n t'')
      | None => None
      end
  | ScenarioEdgeLeaf l =>
      match SetIntersection (FlipEdges l) (stateEdges s) with
      | [] => None
      | l' => Some (ScenarioEdgeLeaf (FlipEdges l'))
      end
  | ScenarioNodeLeaf l =>
      match NodeSetIntersection l (stateNotNodes s) with
      | [] => None
      | l' => Some (ScenarioNodeLeaf l')
      end
  | ScenarioNotNodeLeaf l =>
      match (NodeSetIntersection l (stateNodes s),
        NodeSetIntersection l (stateEdgeNodes s)) with
      | ([], []) => None
      | (l', []) => Some (ScenarioNotNodeLeaf l')
      | ([], l') => Some (ScenarioNotNodeLeaf l')
      | (l1, l2) => Some (ScenarioNotNodeLeaf (app_rev l1 l2))
      end
  | ScenarioAnd a b =>
      match (ScenarioTreeKeepIfFalse s a, ScenarioTreeKeepIfFalse s b) with
      | (Some a', Some b') => Some (ScenarioAnd a' b')
      | (None, Some b') => Some b'
      | (Some a', None) => Some a'
      | (None, None) => None
      end
  | ScenarioOr a b =>
      match (ScenarioTreeKeepIfFalse s a, ScenarioTreeKeepIfFalse s b) with
      | (Some a', Some b') => Some (ScenarioOr a' b')
      | (None, Some b') => None
      | (Some a', None) => None
      | (None, None) => None
      end
  | ScenarioTrue => None
  | ScenarioFalse => Some ScenarioFalse
  end.

Definition EliminateQuantifiers
  (stage_names : list (list string))
  (s : FOLState)
  (f : FOLFormula)
  (l : list FOLTerm)
  : ScenarioTree :=
  let t := EliminateQuantifiersHelper false stage_names s f l in
  (* let t := ScenarioTreeEdgeCountGraph 5 t "QuantifiersRemoved" in *)
  let t' := SimplifyScenarioTree t in
  let t' := ScenarioTreeEdgeCountGraph 5 t' "QuantifiersRemovedAndSimplified" in
  if PrintFlag 0
  then
    if ReducesToFalse t'
    then
      let t'' :=
        match (ScenarioTreeKeepIfFalse s t) with
        | Some t''' => ScenarioTreeEdgeCountGraph 0 t''' "TriviallyFalse"
        | None => Warning ScenarioFalse ["Doesn't reduce to false?"]
        end in
      match t'' with
      | ScenarioTrue => Comment t' ["ScenarioTree unsatisfiable?"]
      | _ => Comment t' ["ScenarioTree unsatisfiable"]
      end
    else t'
  else t'.

Module STBFwdExample.

Definition STBFwdPartial : FOLFormula :=
  FOLAnd (FOLNot (FOLPredicate (PredSameUop "i" "uop")))
   (FOLAnd (FOLPredicate (PredSameVirtualAddress "i" "uop"))
     (FOLAnd (FOLPredicate (PredSameData "i" "uop"))
       (FOLPredicate (PredAddEdges [
         (("i", (SoIInt 0, SoIInt 3)), ("uop", (SoIInt 0, SoIInt 3)), "STBFwd", "red");
         (("uop", (SoIInt 0, SoIInt 3)), ("i", (SoIInt 0, SoIInt 7)), "STBFwd", "red")])
       )
     )
   ).

Definition STBFwd : FOLFormula :=
  FOLExists (MicroopQuantifier "i") STBFwdPartial.

Definition i0 := mkMicroop 0 0 0 0 (Write [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition i1 := mkMicroop 1 0 0 0 (Write [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition i2 := mkMicroop 2 0 0 0 (Read  [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition eState : FOLState := mkFOLState
  [] [] [(i0, (0, 0)); (i1, (0, 0)); (i2, (0, 0))]
  [((i0, (0, 0)), (i1, (0, 0)), "PO", "blue");
   ((i1, (0, 0)), (i2, (0, 0)), "PO", "blue")]
  [i0; i1; i2] [] [] [].
Definition eTerms := [MicroopTerm "uop" i2].

Example e0 : EliminateQuantifiers [] eState
  (FOLPredicate (PredAddEdges [(("uop", (SoIInt 0, SoIInt 0)), ("uop", (SoIInt 0, SoIInt 1)), "label", "red")]))
  eTerms =
  ScenarioEdgeLeaf ([((i2, (0, 0)), (i2, (0, 1)), "label", "red")]).
Proof.
  auto.
Qed.

Example e1 : EliminateQuantifiers [] eState STBFwdPartial
    [MicroopTerm "uop" i2; MicroopTerm "i" i1] =
    ScenarioEdgeLeaf [
      ((i2, (0, 3)), (i1, (0, 7)), "STBFwd", "red");
      ((i1, (0, 3)), (i2, (0, 3)), "STBFwd", "red")].
Proof.
  auto.
Qed.

Example e2 : stateUops eState = [i0; i1; i2].
Proof.
  auto.
Qed.

Example e3 : EliminateQuantifiers [] eState STBFwd eTerms =
  ScenarioOr
    (ScenarioName "i = (inst 0 0 0 0)"
      (ScenarioEdgeLeaf [
        ((i2, (0, 3)), (i0, (0, 7)), "STBFwd", "red");
        ((i0, (0, 3)), (i2, (0, 3)), "STBFwd", "red")]))
    (ScenarioName "i = (inst 1 0 0 0)"
      (ScenarioEdgeLeaf [
        ((i2, (0, 3)), (i1, (0, 7)), "STBFwd", "red");
        ((i1, (0, 3)), (i2, (0, 3)), "STBFwd", "red")])).
Proof.
  auto.
Qed.

End STBFwdExample.

Module BeforeOrAfterExample.

Definition BeforeOrAfter : FOLFormula :=
  FOLForAll (MicroopQuantifier "i1")
    (FOLForAll (MicroopQuantifier "i2")
      (FOLImplies (FOLNot (FOLPredicate (PredSameUop "i1" "i2")))
        (FOLOr
          (FOLPredicate (PredAddEdges [(("i1", (SoIInt 0, SoIInt 0)), ("i2", (SoIInt 0, SoIInt 0)), "x", "red")]))
          (FOLPredicate (PredAddEdges [(("i2", (SoIInt 0, SoIInt 0)), ("i1", (SoIInt 0, SoIInt 0)), "x", "red")]))
        )
      )
    ).

Definition i0 := mkMicroop 0 0 0 0 (Write [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition i1 := mkMicroop 1 0 0 0 (Write [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition i2 := mkMicroop 2 0 0 0 (Read  [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition eState : FOLState := mkFOLState
  [] [] [(i0, (0, 0)); (i1, (0, 0)); (i2, (0, 0))]
  [((i0, (0, 0)), (i1, (0, 0)), "x", "red");
   ((i0, (0, 0)), (i2, (0, 0)), "x", "red")]
  [i0; i1; i2] [] [] [].
Definition eTerms : list FOLTerm := [].

Example e0 :
  EliminateQuantifiers [] eState BeforeOrAfter eTerms =
  ScenarioAnd
    (ScenarioName "i1 = (inst 1 0 0 0)"
      (ScenarioName "i2 = (inst 2 0 0 0)"
        (ScenarioOr (ScenarioEdgeLeaf [(i1, (0, 0), (i2, (0, 0)), "x", "red")])
           (ScenarioEdgeLeaf [(i2, (0, 0), (i1, (0, 0)), "x", "red")]))))
    (ScenarioName "i1 = (inst 2 0 0 0)"
      (ScenarioName "i2 = (inst 1 0 0 0)"
        (ScenarioOr (ScenarioEdgeLeaf [(i2, (0, 0), (i1, (0, 0)), "x", "red")])
           (ScenarioEdgeLeaf [(i1, (0, 0), (i2, (0, 0)), "x", "red")])))).
Proof.
Abort.

End BeforeOrAfterExample.

Fixpoint ReevaluateScenarioTree
  (s : FOLState)
  (t : ScenarioTree)
  : ScenarioTree :=
  match t with
  | ScenarioName n t' => ScenarioName n (ReevaluateScenarioTree s t')
  | ScenarioEdgeLeaf l =>
      if SetIntersectionIsEmpty (FlipEdges l) (stateEdges s)
      then ScenarioEdgeLeaf (SetDifference l (stateEdges s))
      else ScenarioFalse
  | ScenarioNodeLeaf l =>
      if NodeSetIntersectionIsEmpty l (stateNotNodes s)
      then ScenarioNodeLeaf (NodeSetDifference l (stateNodes s))
      else ScenarioFalse
  | ScenarioNotNodeLeaf l =>
      if andb
        (NodeSetIntersectionIsEmpty l (stateNodes s))
        (NodeSetIntersectionIsEmpty l (stateEdgeNodes s))
      then
        match NodeSetDifference l (stateNotNodes s) with
        | [] =>
          (* all nodes in l are already added to the list of forbidden nodes,
           * so we can eliminate this leaf safely *)
          ScenarioTrue
        | l' => ScenarioNotNodeLeaf l'
        end
      else ScenarioFalse
  | ScenarioAnd a b =>
      ScenarioAnd (ReevaluateScenarioTree s a) (ReevaluateScenarioTree s b)
  | ScenarioOr a b =>
      ScenarioOr (ReevaluateScenarioTree s a) (ReevaluateScenarioTree s b)
  | ScenarioTrue => t
  | ScenarioFalse => t
  end.

Fixpoint ScenarioTreeAssignLeaves
  (s : FOLState)
  (t : ScenarioTree)
  : ScenarioTree :=
  match t with
  | ScenarioName n t' => ScenarioName n (ScenarioTreeAssignLeaves s t')
  | ScenarioEdgeLeaf l =>
      if SetIntersectionIsEmpty (FlipEdges l) (stateEdges s)
      then ScenarioTrue
      else ScenarioFalse
  | ScenarioNodeLeaf l =>
      if NodeSetIntersectionIsEmpty l (stateNotNodes s)
      then ScenarioTrue
      else ScenarioFalse
  | ScenarioNotNodeLeaf l =>
      if andb (NodeSetIntersectionIsEmpty l (stateNodes s))
        (NodeSetIntersectionIsEmpty l (stateEdgeNodes s))
      then ScenarioTrue
      else ScenarioFalse
  | ScenarioAnd a b =>
      ScenarioAnd (ScenarioTreeAssignLeaves s a) (ScenarioTreeAssignLeaves s b)
  | ScenarioOr a b =>
      ScenarioOr (ScenarioTreeAssignLeaves s a) (ScenarioTreeAssignLeaves s b)
  | ScenarioTrue => ScenarioTrue
  | ScenarioFalse => ScenarioFalse
  end.

Definition FOLMacro := (string * list string * FOLFormula) % type.

Fixpoint FindMacro
  (name : string)
  (l : list FOLMacro)
  : option (list string * FOLFormula) :=
  match l with
  | (h_name, h_args, h_formula)::t =>
      if beq_string name h_name
      then Some (h_args, h_formula)
      else FindMacro name t
  | [] => Warning None ["Could not find macro "; name]
  end.

Fixpoint ArgsZipHelper
  {A B : Type}
  (a : list A)
  (b : list B)
  (r : list (A * B))
  : list (A * B) :=
  match (a, b) with
  | (h_a::t_a, h_b::t_b) => ArgsZipHelper t_a t_b ((h_a, h_b) :: r)
  | ([], []) => r
  | _ => Warning r ["Macro argument length mismatch!"]
  end.

Definition ArgsZip
  {A B : Type}
  (a : list A)
  (b : list B)
  : list (A * B) :=
  ArgsZipHelper a b [].

Fixpoint FOLExpandMacros
  (d : nat) (* depth *)
  (l : list FOLMacro)
  (f : FOLFormula)
  : FOLFormula :=
  match d with
  | S d' =>
      match f with
      | FOLName s f' => FOLName s (FOLExpandMacros d' l f')
      | FOLExpandMacro s given_args =>
          match FindMacro s l with
          | Some (old_args, m) =>
              let f' := fold_left
                (fun x y => FOLLet (MacroArgTerm (fst y) (snd y)) x)
                (ArgsZip old_args given_args) m in
              FOLName s (FOLExpandMacros d' l f')
          | None => Warning (FOLPredicate PredFalse) ["Macro "; s; " not found!"]
          end
      | FOLPredicate p => FOLPredicate p
      | FOLNot f' => FOLNot (FOLExpandMacros d' l f')
      | FOLOr a b => FOLOr (FOLExpandMacros d' l a) (FOLExpandMacros d' l b)
      | FOLAnd a b => FOLAnd (FOLExpandMacros d' l a) (FOLExpandMacros d' l b)
      | FOLForAll q f' => FOLForAll q (FOLExpandMacros d' l f')
      | FOLExists q f' => FOLExists q (FOLExpandMacros d' l f')
      | FOLLet t f' => FOLLet t (FOLExpandMacros d' l f')
      end
  | O => Warning (FOLPredicate PredFalse) ["Recursion depth exceeded!"]
  end.

Definition CheckFinalState
  (stage_names : list (list string))
  (arch_edges : list ArchitectureLevelEdge)
  (check_nodes : bool)
  (s : FOLState)
  : bool :=
  match Topsort (stateEdges s) with
  | ReverseTotalOrder _ =>
    let nodes := NodesFromEdges (stateEdges s) in
    if negb (NodeSetIntersectionIsEmpty (stateNotNodes s) nodes)
    then
      let result := false in
      if PrintFlag 1
      then Comment result ["ScenarioTree converged, but forbidden nodes were used"]
      else result
    else
    if check_nodes
    then
      match NodeSetDifference (stateNodes s) (NodesFromEdges (stateEdges s)) with
      | _::_  =>
          let result := false in
          if PrintFlag 1
          then Comment result ["ScenarioTree converged, but required nodes were missing"]
          else result
      | [] =>
          let result := true in
          if PrintFlag 1
          then Comment result ["ScenarioTree converged"]
          else result
      end
    else
      let result := true in
      if PrintFlag 1
      then Comment result ["ScenarioTree converged"]
      else result
  | _ =>
    let result := false in
    if PrintFlag 1
    then Comment result
      ("ScenarioTree converged, but graph is cyclic" :: newline ::
        (GraphvizCompressedGraph "DeadEnd" stage_names (stateEdges s) [] arch_edges))
    else result
  end.

Fixpoint ScenarioTreeCheckNodes
  (s : FOLState)
  (t : ScenarioTree)
  : ScenarioTree :=
  match t with
  | ScenarioName n t' =>
      match ScenarioTreeCheckNodes s t' with
      | ScenarioTrue => ScenarioTrue
      | ScenarioFalse => ScenarioFalse
      | t'' => ScenarioName n (t'')
      end
  | ScenarioEdgeLeaf [] => ScenarioTrue
  | ScenarioNodeLeaf [] => ScenarioTrue
  | ScenarioNotNodeLeaf [] => ScenarioFalse
  | ScenarioEdgeLeaf l => t
  | ScenarioNodeLeaf l => ScenarioTrue
  | ScenarioNotNodeLeaf l => ScenarioTrue
  | ScenarioAnd a b =>
      ScenarioAnd (ScenarioTreeCheckNodes s a) (ScenarioTreeCheckNodes s b)
  | ScenarioOr a b =>
      ScenarioOr (ScenarioTreeCheckNodes s a) (ScenarioTreeCheckNodes s b)
  | ScenarioTrue => ScenarioTrue
  | ScenarioFalse => ScenarioFalse
  end.

Fixpoint ReevaluateScenarioTreeIterator
  (n : nat)
  (stage_names : list (list string))
  (arch_edges : list ArchitectureLevelEdge)
  (s : FOLState)
  (t : ScenarioTree)
  : FOLState * ScenarioTree :=
  (* Re-evaluate the constraints given the current graph, and prune out
   * any which are no longer valid *)
  let t'' := ReevaluateScenarioTree s t in
  let t'' := ScenarioTreeEdgeCountGraph 5 t'' "ScenarioCounts_StillIterating_NotSimplified" in
  (* Simplify the remaining tree *)
  let t' := SimplifyScenarioTree t'' in
  let t' := ScenarioTreeEdgeCountGraph 3 t' "ScenarioCounts_StillIterating_Simplified" in
  (* Check if this is a valid solution *)
  if andb (ReducesToTrue t') (CheckFinalState stage_names arch_edges true s)
  then
    let result := (s, ScenarioTrue) in
    if PrintFlag 1
    then Comment result ["ScenarioTree converged and completed"]
    else result
  else
  (* Check if this is a dead end *)
  if ReducesToFalse t'
  then
    let result := (s, t') in
    if PrintFlag 1
    then
      let t'' :=
        match (ScenarioTreeKeepIfFalse s t) with
        | Some t''' =>
          let t''' :=
            if PrintFlag 1
            then
              let t''' := Comment t''' ("Reached dead end" :: newline ::
              (GraphvizCompressedGraph "DeadEnd" stage_names (stateEdges s) [] arch_edges)) in
              match FindBranchingEdges t''' with
              | Some cases =>
                let f a b :=
                  let g' := app_rev (stateEdges s) b in
                  Printf a (StringOf
                    (GraphvizCompressedGraph "DeadEndBranch" stage_names g' [] arch_edges)) in
                fold_left f cases t'''
              | None => Comment t''' ["No branching edges at dead end?"]
              end
            else t''' in
            ScenarioTreeEdgeCountGraph 1 t''' "ReducesToFalse"
        | None => Warning ScenarioFalse ["Doesn't reduce to false?"]
        end in
      match t'' with
      | ScenarioTrue => Comment result ["ScenarioTree unsatisfiable?"]
      | _ => Comment result ["ScenarioTree unsatisfiable"]
      end
    else result
  else
  (* Neither TRUE nor FALSE; need to keep evaluating *)
  match GuaranteedEdges t' with
  | ([], [], []) =>
      (* The unit propagation has converged; return *)
      if CheckFinalState stage_names arch_edges false s
      then
        let result := (s, t') in
        if PrintFlag 1
        then Comment result ["ReevaluateScenarioTree converged but not completed"]
        else result
      else
        let result := (s, ScenarioFalse) in
        if PrintFlag 1
        then Comment result ["ReevaluateScenarioTree converged, but graph is invalid"]
        else result
  | (n1, n2, e1) =>
    (* The unit propagation hasn't yet converged *)
    match TransitiveClosure (app_rev (stateEdges s) e1) with
    | TC x =>
        (* Still no cycle; so recurse to continue unit propagation *)
        let e1' := EdgesFromAdjacencyList x in
        let n1' := app_rev (stateNodes s) n1 in
        let n2' := app_rev (stateNotNodes s) n2 in
        let s' := FOLStateReplaceEdges s n1' n2' e1' in
        let s' :=
          if PrintFlag 6
          then Comment s' [stringOfNat (List.length n1'); " required nodes"]
          else s' in
        let s' :=
          if PrintFlag 6
          then Comment s' [stringOfNat (List.length n2'); " forbidden nodes"]
          else s' in
        (* Recurse *)
        match n with
        | S n' =>
            let s' :=
              if PrintFlag 2
              then Comment s'
                ("ReevaluateScenarioTreeIterator iterating" :: newline ::
                (GraphvizCompressedGraph "Iterating" stage_names
                  (stateEdges s') (SetDifference (stateEdges s') (stateEdges s))
                  arch_edges))
              else s' in
            ReevaluateScenarioTreeIterator n' stage_names arch_edges s' t'
         | 0 => Warning (s, ScenarioFalse)
             ["ReevaluateScenarioTree Iteration limit exceeded!"]
        end
    | TCError e' =>
        (* Adding these edges would form a cycle: fail *)
        let result := (UpdateFOLState true s e', ScenarioFalse) in
        if PrintFlag 1
        then
          let f a b := Comment a [StringOfGraphEdge b] in
          let result := fold_left f e' result in
          Comment result ("Graph is now cyclic; pruning." :: newline ::
            (GraphvizCompressedGraph "DeadEnd" stage_names
              (stateEdges (fst result)) [] arch_edges))
        else result
    end
  end.

Definition StringOfCase
  (l : list GraphEdge)
  : string :=
    fold_left (fun a b => StringOf [a; newline; "// "; StringOfGraphEdge b]) l
      (StringOf [newline; "// Case:"]).

Fixpoint StringOfDPLLState
  (h : nat * nat)
  : string :=
  let (h1, h2) := h in
  StringOf [" ("; stringOfNat h1; "/"; stringOfNat h2; ")"].

Fixpoint NegateScenarioTree
  (t : ScenarioTree)
  : ScenarioTree :=
  match t with
  | ScenarioName s t' => ScenarioName s (NegateScenarioTree t')
  | ScenarioAnd a b =>
      ScenarioOr (NegateScenarioTree a) (NegateScenarioTree b)
  | ScenarioOr a b =>
      ScenarioAnd (NegateScenarioTree a) (NegateScenarioTree b)
  | ScenarioEdgeLeaf l => fold_left FoldFlipEdge l ScenarioFalse
  | ScenarioNodeLeaf l => ScenarioNotNodeLeaf l
  | ScenarioNotNodeLeaf l => ScenarioNodeLeaf l
  | ScenarioTrue => ScenarioFalse
  | ScenarioFalse => ScenarioTrue
  end.

Fixpoint FOL_DPLL
  (n : nat)
  (arch_edges : list ArchitectureLevelEdge)
  (path : list (nat * nat))
  (stage_names : list (list string))
  (s : FOLState)
  (t : ScenarioTree)
  : option FOLState :=
  match n with
  | S n' =>
    (* Depending on the backend, print a status update every once in a while *)
    let s :=
      if orb (PrintFlag 5) (TimeForStatusUpdate 1)
      then CommentFlush s ("Progress: " :: Map StringOfDPLLState (rev_append path []))
      else s in
    (* Evaluate one step *)
    match ReevaluateScenarioTreeIterator 100 stage_names arch_edges s t with
    | (s', t') =>
      (* Debug output *)
      let t' := ScenarioTreeEdgeCountGraph 3 t' "ScenarioCounts" in
      let t' :=
        if PrintFlag 1
        then Comment t' ("Graph is:" :: newline ::
          (GraphvizCompressedGraph
            (StringOf ("Converged: " ::
              (Map StringOfDPLLState (rev_append path []))))
            stage_names
            (stateEdges s') [] arch_edges))
        else t' in
      (* Check if the graph reduces to TRUE or FALSE *)
      let t'' := ScenarioTreeCheckNodes s' t' in
      let t'' := ScenarioTreeEdgeCountGraph 3 (SimplifyScenarioTree t'')
        "BranchingEdges" in
      if ReducesToTrue  t'' then Some s' else
      if ReducesToFalse t''
      then
        if PrintFlag 1
        then
          (* Debug: find and display the constraints that caused the problem *)
          let t := ScenarioTreeEdgeCountGraph 5 (ScenarioTreeAssignLeaves s' t')
            "PreUnsatisfiableConstraints" in
          let t''' :=
          match ScenarioTreeKeepIfFalse s t with
          | Some t''' =>
              ScenarioTreeEdgeCountGraph 3 t''' "UnsatisfiableConstraints"
          | None =>
              match Topsort (stateEdges s') with
              | ReverseTotalOrder _ => Warning
                  (ScenarioTreeEdgeCountGraph 1 t' "UnsatisfiableConstraints")
                  ["Disagreement on whether tree reduces to false?"]
              | _ => ScenarioName "Cyclic" ScenarioFalse
              end
          end in
          match t''' with
          | ScenarioTrue => Warning None ["Tree reduced to false?"]
          | _ =>
              if PrintFlag 2
              then Comment None ["Tree reduced to false"]
              else None
          end
        else None
      else
      (* Neither TRUE nor FALSE: find a set of branching edges *)
      match FindBranchingEdges t'' with
      | Some cases =>
        let cases :=
          if PrintFlag 1
          then
            Comment cases ["DPLL Found ";
            stringOfNat (List.length cases); " to consider";
            StringOf (Map StringOfCase cases)]
          else cases in
        (* For each branching edge, recursively evaluate the graph with
         * this edge added.  If a branch doesn't work, add the opposite
         * of that edge as a learned conflict term. *)
        let f_fold
          (a : option FOLState * ScenarioTree * nat) (b : list GraphEdge) :=
          let '(a1, a2, a3) := a in
          match a1 with
          | Some _ =>
              (* Found a solution down a previous branch: return it, and don't
               * evaluate further *)
              (a1, ScenarioFalse, S a3)
          | None =>
              (* Add the edge to the current graph *)
              let s'' := UpdateFOLState false s' b in
              let new_path := ((a3, List.length cases) :: path) in
              (* Debug output *)
              let s'' :=
                if PrintFlag 1
                then Comment s'' ("DPLL considering case in which the " ::
                  "following edges were added:" :: StringOfCase b :: newline ::
                  (GraphvizCompressedGraph
                    (StringOf ["Considering Case ";
                      StringOf (Map StringOfDPLLState (rev_append new_path []));
                      " ("; stringOfNat (List.length b);
                      " edge(s), depth="; stringOfNat n; ")"])
                    stage_names (stateEdges s'') b arch_edges))
                else s'' in
              (* Add the current branch as a mandatory constraint, so that
               * recursive steps will follow that branch *)
              let new_tree := ScenarioAnd a2 t' in
              (* Add constraints representing the conflicts learned from
               * previous failed branches *)
              let new_conflict := ScenarioAnd a2
                (NegateScenarioTree (ScenarioEdgeLeaf b)) in
              (* Recurse *)
              (FOL_DPLL n' arch_edges new_path stage_names s'' new_tree, new_conflict, S a3)
          end in
        (* Loop over each branch in the branching set *)
        fst (fst (fold_left f_fold cases (None, ScenarioTrue, 0)))
      | None =>
        Warning None ["DPLL could not find branching edges!"]
      end
    end
  | 0 =>
      (* Oops!  Recursed too deep! *)
      let t := ScenarioTreeEdgeCountGraph 3 t "ScenarioCounts" in
      let t := ScenarioTreeEdgeCountGraph 1
        (SimplifyScenarioTree (ScenarioTreeCheckNodes s t))
        "BranchingEdges" in
      match t with
      | ScenarioTrue => Warning (Some s) ["FOL_DPLL iteration limit reached TRUE!"]
      | _ => Warning (Some s) ["FOL_DPLL iteration limit reached!"]
      end
  end.

Inductive FOLStatement : Set :=
| FOLAxiom : FOLFormula -> FOLStatement
| FOLMacroDefinition : FOLMacro -> FOLStatement
| FOLContextTerm : FOLTerm -> FOLStatement.

Fixpoint AddContext
  (core : nat)
  (c : list FOLTerm)
  (f : FOLFormula)
  : FOLFormula :=
  match c with
  | h::t => FOLLet h (AddContext core t f)
  | [] => f
  end.

Fixpoint EvaluateFOLStatementsHelper
  (core : nat)
  (m : list FOLMacro)
  (c : list FOLTerm)
  (f : FOLFormula)
  (l : list FOLStatement)
  : FOLFormula :=
  match l with
  | (FOLAxiom f')::t => EvaluateFOLStatementsHelper core m c (FOLAnd f f') t
  | (FOLMacroDefinition m')::t => EvaluateFOLStatementsHelper core (m' :: m) c f t
  | (FOLContextTerm c')::t => EvaluateFOLStatementsHelper core m (AddTerm c c') f t
  | [] => FOLExpandMacros MacroExpansionDepth m (AddContext core c f)
  end.

Definition EvaluateFOLStatements
  (c : nat)
  (l : list FOLStatement)
  : FOLFormula :=
  EvaluateFOLStatementsHelper c [] [IntTerm "c" c] (FOLPredicate PredTrue) l.

Definition MicroarchitecturalComponent := list FOLStatement.

Definition Microarchitecture := list MicroarchitecturalComponent.

Fixpoint BuildMicroarchitectureHelper
  (l : list MicroarchitecturalComponent)
  (c : nat)
  : FOLFormula :=
  match l with
  | [] => FOLPredicate PredFalse
  | [h] =>
      let result := EvaluateFOLStatements c h in
      PrintGraphvizStringOfFOLFormula result
  | h::t =>
      let result := EvaluateFOLStatements c h in
      let result := PrintGraphvizStringOfFOLFormula result in
      FOLAnd result (BuildMicroarchitectureHelper t (S c))
  end.

Fixpoint BuildMicroarchitecture
  (m : Microarchitecture)
  : FOLFormula :=
  BuildMicroarchitectureHelper m 0.

Fixpoint SetNth
  {A : Type}
  (n : nat)
  (l : list (option A))
  (a : A)
  : list (option A) :=
  match (n, l) with
  | (S n', h::t) => h      :: SetNth n' t  a
  | (S n', []  ) => None   :: SetNth n' [] a
  | (O   , h::t) => Some a :: t
  | (O   , []  ) => [Some a]
  end.

Fixpoint StageNamesRemoveOptions
  (l : list (option string))
  : list string :=
  match l with
  | Some h :: t => h         :: StageNamesRemoveOptions t
  | None   :: t => "Unknown" :: StageNamesRemoveOptions t
  | []          => []
  end.

Fixpoint StageNamesHelper
  (m : MicroarchitecturalComponent)
  (l : list (option string))
  : list string :=
  match m with
  | FOLContextTerm (StageNameTerm s n)::t =>
      StageNamesHelper t (SetNth n l s)
  | _::t => StageNamesHelper t l
  | [] => StageNamesRemoveOptions l
  end.

Fixpoint StageNames
  (m : Microarchitecture)
  : list (list string) :=
  match m with
  | h::t => StageNamesHelper h [] :: StageNames t
  | [] => []
  end.

Fixpoint EvaluateUHBGraphs
  (max_depth : nat)
  (m : Microarchitecture)
  (programs : list (list Microop * list ArchitectureLevelEdge * list BoundaryCondition))
  (initial : list BoundaryCondition)
  : option (list GraphEdge * list ArchitectureLevelEdge) :=
  match programs with
  | (h_ops, h_edges, h_final)::t =>
    let s := (mkFOLState [] [] [] [] h_ops initial h_final h_edges) in
    let t' := EliminateQuantifiers (StageNames m) s (BuildMicroarchitecture m) [] in
    match FOL_DPLL max_depth h_edges [] (StageNames m) s t' with
    | Some s =>
        let result := Some (stateEdges s, h_edges) in
        if PrintFlag 0
        then Comment result
          ("Evaluated to Observable" :: newline ::
          (GraphvizCompressedGraph "Final" (StageNames m)
            (stateEdges s) [] h_edges))
        else Comment result ["Evaluated to observable"]
    | None => EvaluateUHBGraphs max_depth m t initial
    end
  | [] =>
      if PrintFlag 0
      then Comment None ["Evaluated to Non-observable"]
      else None
  end.

Inductive ExpectedResult : Set :=
  Permitted | Forbidden | Required | Unobserved.
