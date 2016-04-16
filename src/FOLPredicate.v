Require Import List.
Require Import String.
Require Import PipeGraph.Debug.
Require Import PipeGraph.StringUtil.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Graph.

Import ListNotations.
Open Scope string_scope.

Inductive StringOrInt : Set :=
| SoISum : StringOrInt -> StringOrInt -> StringOrInt
| SoIString : string -> StringOrInt
| SoIInt : nat -> StringOrInt
| SoICoreID : string -> StringOrInt.

Fixpoint StringOfSoI
  (soi : StringOrInt)
  : string :=
  match soi with
  | SoISum a b => StringOf ["("; StringOfSoI a; ")+("; StringOfSoI b; ")"]
  | SoIString s => s
  | SoIInt n => stringOfNat n
  | SoICoreID s => StringOf ["CoreOf "; s]
  end.

Definition PredGraphNode := (string * (StringOrInt * StringOrInt)) % type.
Definition PredGraphEdge := (PredGraphNode * PredGraphNode * string * string) % type.

Definition StringOfPredGraphNode
  (n : PredGraphNode)
  : string :=
  match n with
  | (s1, (s2, s3)) =>
      StringOf ["("; s1; ", ("; StringOfSoI s2; ", "; StringOfSoI s3; "))"]
  end.

Definition StringOfPredGraphEdge
  (e : PredGraphEdge)
  : string :=
  match e with
  | (s, d, l, c) =>
      StringOf ["("; StringOfPredGraphNode s; " --"; l; "--> ";
        StringOfPredGraphNode d]
  end.

Inductive FOLPredicateType :=
| PredDebug : string -> FOLPredicateType
| PredHasDependency : string -> string -> string -> FOLPredicateType
| PredIsRead : string -> FOLPredicateType
| PredIsWrite : string -> FOLPredicateType
| PredIsAPICAccess : string -> string -> FOLPredicateType
| PredIsFence : string -> FOLPredicateType
| PredAccessType : string -> string -> FOLPredicateType
| PredSameUop : string -> string -> FOLPredicateType
| PredSameNode : string -> string -> FOLPredicateType
| PredSameCore : StringOrInt -> StringOrInt -> FOLPredicateType
| PredSmallerGlobalID : string -> string -> FOLPredicateType
| PredSameGlobalID : string -> string -> FOLPredicateType
| PredSameIntraInstID : string -> string -> FOLPredicateType
| PredSameThread : StringOrInt -> StringOrInt -> FOLPredicateType
| PredOnCore : StringOrInt -> string -> FOLPredicateType
| PredOnThread : StringOrInt -> string -> FOLPredicateType
| PredSameVirtualAddress : string -> string -> FOLPredicateType
| PredSamePhysicalAddress : string -> string -> FOLPredicateType
| PredSameVirtualTag : string -> string -> FOLPredicateType
| PredSamePhysicalTag : string -> string -> FOLPredicateType
| PredSameIndex : string -> string -> FOLPredicateType
| PredKnownData : string -> FOLPredicateType
| PredSameData : string -> string -> FOLPredicateType
| PredDataFromPAInitial : string -> FOLPredicateType
| PredDataFromPAFinal : string -> FOLPredicateType
| PredSamePAasPTEforVA : string -> string -> FOLPredicateType
| PredDataIsCorrectTranslation : AccessedStatus -> DirtyStatus -> string -> string -> FOLPredicateType
| PredTranslationMatchesInitialState : AccessedStatus -> DirtyStatus -> string -> FOLPredicateType
| PredProgramOrder : string -> string -> FOLPredicateType
| PredConsec : string -> string -> FOLPredicateType
| PredAddEdges : list PredGraphEdge -> FOLPredicateType
| PredEdgesExist : list PredGraphEdge -> FOLPredicateType
| PredNodesExist : list PredGraphNode -> FOLPredicateType
| PredTrue : FOLPredicateType
| PredFalse : FOLPredicateType
| PredHasID : nat -> nat -> nat -> nat -> string -> FOLPredicateType
| PredHasGlobalID : nat -> string -> FOLPredicateType.

Definition stringOfPredicate
  (verbose : bool)
  (p : FOLPredicateType)
  : string :=
  match p with
  | PredDebug a                          => StringOf ["Debug "; a]
  | PredHasDependency a b c              =>
    StringOf ["HasDependency "; a; " "; b; " "; c]
  | PredIsRead a                         => StringOf ["IsRead "; a]
  | PredIsWrite a                        => StringOf ["IsWrite "; a]
  | PredIsFence a                        => StringOf ["IsFence "; a]
  | PredIsAPICAccess a b                 => StringOf ["IsAPICAccess "; a; " "; b]
  | PredAccessType a b                   => StringOf ["AccessType "; a; " "; b]
  | PredSameUop a b                      => StringOf ["SameUop "; a; " "; b]
  | PredSameNode a b                     => StringOf ["SameNode "; a; " "; b]
  | PredSameCore a b                     =>
      StringOf ["SameCore "; StringOfSoI a; " "; StringOfSoI b]
  | PredSmallerGlobalID a b              => StringOf ["SmallerGlobalID "; a; " "; b]
  | PredSameGlobalID a b                 => StringOf ["SameGlobalID "; a; " "; b]
  | PredSameIntraInstID a b              => StringOf ["SameIntraInstructionID "; a; " "; b]
  | PredOnCore a b                       => StringOf ["OnCore "; StringOfSoI a; " "; b]
  | PredSameThread a b                   =>
      StringOf ["SameThread "; StringOfSoI a; " "; StringOfSoI b]
  | PredOnThread a b                     => StringOf ["OnThread "; StringOfSoI a; " "; b]
  | PredSameVirtualAddress a b           => StringOf ["SameVA "; a; " "; b]
  | PredSamePhysicalAddress a b          => StringOf ["SamePA "; a; " "; b]
  | PredSameVirtualTag a b               => StringOf ["SameVTag "; a; " "; b]
  | PredSamePhysicalTag a b              => StringOf ["SamePTag "; a; " "; b]
  | PredSameIndex a b                    => StringOf ["SameIndex "; a; " "; b]
  | PredKnownData a                      => StringOf ["KnownData "; a]
  | PredSameData a b                     => StringOf ["SameData "; a; " "; b]
  | PredDataFromPAInitial a              => StringOf ["DataFromInitialStateAtPA "; a]
  | PredDataFromPAFinal a                => StringOf ["DataFromFinalStateAtPA "; a]
  | PredSamePAasPTEforVA a b             => StringOf ["SamePAasPTEforVA "; a; " "; b]
  | PredDataIsCorrectTranslation a b c d =>
      StringOf ["DataIsCorrectTranslation "; StringOfAccessedStatus a; " ";
        StringOfDirtyStatus b; " "; c; " "; d]
  | PredTranslationMatchesInitialState a b c =>
      StringOf ["TranslationMatchesInitialState "; StringOfAccessedStatus a; " ";
        StringOfDirtyStatus b; " "; c]
  | PredProgramOrder a b                 => StringOf ["ProgramOrder "; a; " "; b]
  | PredConsec a b                       => StringOf ["Consec "; a; " "; b]
  | PredAddEdges l                       =>
      if verbose
      then StringOf ["AddEdges (\n";
        fold_left (fun a b => StringOf [a; StringOfPredGraphEdge b; "\n"]) l "";
        ")"]
      else StringOf ["AddEdges (...)"]
  | PredEdgesExist l                     => StringOf ["EdgesExist (...)"]
  | PredNodesExist l                     => StringOf ["NodesExist (...)"]
  | PredTrue                             => StringOf ["TRUE"]
  | PredFalse                            => StringOf ["FALSE"]
  | PredHasID a b c d e                  => StringOf ["HasID ";
      stringOfNat a; " "; stringOfNat b; " "; stringOfNat c; " ";
      stringOfNat d; " "; e]
  | PredHasGlobalID a b                  => StringOf ["HasGlobalID ";
      stringOfNat a; " "; b]
  end.

Definition FOLLookupPredicate_IIIIS
  (name : string)
  (a b c d : nat)
  (e : string)
  : FOLPredicateType :=
       if beq_string name "HasID" then PredHasID a b c d e
  else Warning PredFalse ["Predicate "; name; " not found!"].

Definition FOLLookupPredicate_SSS
  (name : string)
  (a b c : string)
  : FOLPredicateType :=
       if beq_string name "HasDependency" then PredHasDependency a b c
  else Warning PredFalse ["Predicate "; name; " not found!"].

Definition FOLLookupPredicate_IS
  (name : string)
  (a : nat)
  (b : string)
  : FOLPredicateType :=
       if beq_string name "SameCore"    then PredSameCore (SoIInt a) (SoIString b)
  else if beq_string name "SameThread"  then PredSameThread (SoIInt a) (SoIString b)
  else if beq_string name "OnCore"      then PredOnCore (SoIInt a) b
  else if beq_string name "OnThread"    then PredOnThread (SoIInt a) b
  else if beq_string name "HasGlobalID" then PredHasGlobalID a b
  else Warning PredFalse ["Predicate "; name; " not found!"].

Definition FOLLookupPredicate_ADSS
  (name : string)
  (a : AccessedStatus)
  (b : DirtyStatus)
  (c d : string)
  : FOLPredicateType :=
       if beq_string name "DataIsCorrectTranslation"  then
         PredDataIsCorrectTranslation a b c d
  else Warning PredFalse ["Predicate "; name; " not found!"].

Definition FOLLookupPredicate_ADS
  (name : string)
  (a : AccessedStatus)
  (b : DirtyStatus)
  (c : string)
  : FOLPredicateType :=
  if beq_string name "TranslationMatchesInitialState"       then PredTranslationMatchesInitialState a b c
  else Warning PredFalse ["Predicate "; name; " not found!"].

Definition FOLLookupPredicate_SS
  (name : string)
  (a b : string)
  : FOLPredicateType :=
       if beq_string name "IsAPICAccess"              then PredIsAPICAccess a b
  else if beq_string name "FenceType"                 then PredAccessType a b
  else if beq_string name "AccessType"                then PredAccessType a b
  else if beq_string name "SameMicroop"               then PredSameUop a b
  else if beq_string name "SameCore"                  then PredSameCore (SoIString a) (SoIString b)
  else if beq_string name "SmallerGlobalID"           then PredSmallerGlobalID a b
  else if beq_string name "SameGlobalID"              then PredSameGlobalID a b
  else if beq_string name "SameIntraInstructionID"    then PredSameIntraInstID a b
  else if beq_string name "OnCore"                    then PredOnCore (SoIString a) b
  else if beq_string name "SameThread"                then PredSameThread (SoIString a) (SoIString b)
  else if beq_string name "OnThread"                  then PredOnThread (SoIString a) b
  else if beq_string name "SameVirtualAddress"        then PredSameVirtualAddress a b
  else if beq_string name "SamePhysicalAddress"       then PredSamePhysicalAddress a b
  else if beq_string name "SameVirtualTag"            then PredSameVirtualTag a b
  else if beq_string name "SamePhysicalTag"           then PredSamePhysicalTag a b
  else if beq_string name "SameIndex"                 then PredSameIndex a b
  else if beq_string name "SameData"                  then PredSameData a b
  else if beq_string name "SamePAasPTEforVA"          then PredSamePAasPTEforVA a b
  else if beq_string name "DataIsCorrectTranslation"  then
    let result :=
      PredDataIsCorrectTranslation AccessedDontCare DirtyDontCare a b in
    Warning result
      ["DataIsCorrectTranslation: assuming accessed and dirty are don't cares"]
  else if beq_string name "ConsecutiveMicroops"       then PredConsec a b
  else if beq_string name "ProgramOrder"              then PredProgramOrder a b
  else Warning PredFalse ["Predicate "; name; " not found!"].

Definition FOLLookupPredicate_S
  (name : string)
  (a : string)
  : FOLPredicateType :=
       if beq_string name "Debug"                          then PredDebug a
  else if beq_string name "IsRead"                         then PredIsRead a
  else if beq_string name "IsAnyRead"                      then PredIsRead a
  else if beq_string name "IsWrite"                        then PredIsWrite a
  else if beq_string name "IsAnyWrite"                     then PredIsWrite a
  else if beq_string name "IsFence"                        then PredIsFence a
  else if beq_string name "IsAnyFence"                     then PredIsFence a
  else if beq_string name "KnownData"                      then PredKnownData a
  else if beq_string name "DataFromInitialStateAtPA"       then PredDataFromPAInitial a
  else if beq_string name "DataFromFinalStateAtPA"         then PredDataFromPAFinal a
  else if beq_string name "TranslationMatchesInitialState" then
    let result :=
      PredTranslationMatchesInitialState AccessedDontCare DirtyDontCare a in
    Warning result
      ["TranslationMatchesInitialState: assuming accessed and dirty are don't cares"]
  else Warning PredFalse ["Predicate "; name; " not found!"].

Definition FOLLookupPredicate_E
  (name : string)
  (e : PredGraphEdge)
  : FOLPredicateType :=
       if beq_string name "AddEdge"    then PredAddEdges [e]
  else if beq_string name "EdgeExists" then PredEdgesExist [e]
  else Warning PredFalse ["Predicate "; name; " not found!"].

Definition FOLLookupPredicate_N
  (name : string)
  (n : PredGraphNode)
  : FOLPredicateType :=
  if beq_string name "NodeExists" then PredNodesExist [n]
  else Warning PredFalse ["Predicate "; name; " not found!"].

Definition FOLLookupPredicate_lE
  (name : string)
  (e : list PredGraphEdge)
  : FOLPredicateType :=
       if beq_string name "AddEdges"   then PredAddEdges e
  else if beq_string name "EdgesExist" then PredEdgesExist e
  else Warning PredFalse ["Predicate "; name; " not found!"].

Definition FOLLookupPredicate_lN
  (name : string)
  (n : list PredGraphNode)
  : FOLPredicateType :=
       if beq_string name "NodesExist" then PredNodesExist n
  else Warning PredFalse ["Predicate "; name; " not found!"].

