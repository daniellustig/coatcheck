%{
  open Lexing
%}
%token <int> INT
%token <string> STRING
%token DEFINEMACRO EXPANDMACRO STAGENAME
%token AXIOM
%token MICROOP CORE THREAD
%token READ WRITE RMWREAD RMWWRITE FENCE
%token FORALL EXISTS
%token COMMA PERIOD COLON SEMICOLON QUOTE
%token AND OR NOT IMPLIES IFF
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token ANYNAME WITH AS
%token EOF
%token PLUS
%token COREID
%token ACCESSED NOTACCESSED ACCESSEDDONTCARE
%token DIRTY NOTDIRTY DIRTYDONTCARE
%nonassoc FORALL EXISTS COMMA
%nonassoc IFF
%right IMPLIES
%right OR
%right AND
%nonassoc NOT
%left PLUS
%start main
%type <PipeGraph.microarchitecturalComponent> main
%%

main:
  statements EOF {$1};

statements:
  | statements statement {$1 @ [$2]}
  | statement {[$1]};

statement:
  | axiom {PipeGraph.FOLAxiom ($1)}
  | macro {PipeGraph.FOLMacroDefinition ($1)}
  | contextterm {PipeGraph.FOLContextTerm ($1)};

contextterm:
  STAGENAME INT qstring PERIOD {PipeGraph.StageNameTerm($3, $2)};

axiom:
  AXIOM qstring COLON formula PERIOD {PipeGraph.FOLName ($2, $4)};

macro:
  | DEFINEMACRO qstring args COLON formula PERIOD
    {PipeGraph.Pair(PipeGraph.Pair($2, $3), $5)}
  | DEFINEMACRO qstring COLON formula PERIOD
    {PipeGraph.Pair(PipeGraph.Pair($2, []), $4)}

args:
  | args STRING {$1 @ [$2]}
  | STRING {[$1]};

params:
  | params string_or_int {$1 @ [$2]}
  | string_or_int {[$1]};

qstring:
  | QUOTE str QUOTE {$2}
  | QUOTE QUOTE {""};

str:
  STRING {$1};

formula:
  | LPAREN str COLON formula RPAREN {PipeGraph.FOLName ($2, $4)}
  | EXPANDMACRO str params {PipeGraph.FOLExpandMacro ($2, $3)}
  | EXPANDMACRO str {PipeGraph.FOLExpandMacro ($2, [])}
  | LPAREN formula RPAREN {$2}
  | predicate {PipeGraph.FOLPredicate $1}
  | NOT formula {PipeGraph.FOLNot $2}
  | formula AND formula {PipeGraph.FOLAnd ($1, $3)}
  | formula OR formula {PipeGraph.FOLOr ($1, $3)}
  | formula IMPLIES formula {PipeGraph.fOLImplies $1 $3}
  | formula IFF formula {PipeGraph.fOLIff $1 $3}
  | EXISTS quantifier COMMA formula {PipeGraph.FOLExists ($2, $4)}
  | FORALL quantifier COMMA formula {PipeGraph.FOLForAll ($2, $4)}
  | WITH MICROOP INT AS qstring COMMA formula
    {
      PipeGraph.FOLExists (PipeGraph.microopQuantifier($5),
        PipeGraph.FOLAnd
          (PipeGraph.FOLPredicate(PipeGraph.PredHasGlobalID($3, $5)), $7))
    };

quantifier:
  | MICROOP qstring {PipeGraph.microopQuantifier($2)}
  | CORE qstring {PipeGraph.coreQuantifier($2)};
  | THREAD qstring {PipeGraph.threadQuantifier($2)};

accessedStatus:
  | ACCESSED {PipeGraph.Accessed}
  | NOTACCESSED {PipeGraph.NotAccessed}
  | ACCESSEDDONTCARE {PipeGraph.AccessedDontCare};

dirtyStatus:
  | DIRTY {PipeGraph.Dirty}
  | NOTDIRTY {PipeGraph.NotDirty}
  | DIRTYDONTCARE {PipeGraph.DirtyDontCare};

predicate:
  | str INT INT INT INT str {PipeGraph.fOLLookupPredicate_IIIIS $1 $2 $3 $4 $5 $6}
  | str str str str {PipeGraph.fOLLookupPredicate_SSS $1 $2 $3 $4}
  | str str str {PipeGraph.fOLLookupPredicate_SS $1 $2 $3}
  | str accessedStatus dirtyStatus str str
    {PipeGraph.fOLLookupPredicate_ADSS $1 $2 $3 $4 $5}
  | str accessedStatus dirtyStatus str
    {PipeGraph.fOLLookupPredicate_ADS $1 $2 $3 $4}
  | str INT str {PipeGraph.fOLLookupPredicate_IS $1 $2 $3}
  | str str {PipeGraph.fOLLookupPredicate_S $1 $2}
  | str edge {PipeGraph.fOLLookupPredicate_E $1 $2}
  | str edgelist {PipeGraph.fOLLookupPredicate_lE $1 $2}
  | str node {PipeGraph.fOLLookupPredicate_N $1 $2}
  | str nodelist {PipeGraph.fOLLookupPredicate_lN $1 $2};

edgelist:
  LBRACKET edges RBRACKET {$2};

edges:
  | edges SEMICOLON edge {$1 @ [$3]}
  | edge {[$1]};

edge:
  | LPAREN node COMMA node COMMA qstring RPAREN
    {
      let startpos = Parsing.symbol_start_pos() in
      let linenum = string_of_int startpos.pos_lnum in
      PipeGraph.Pair(PipeGraph.Pair(PipeGraph.Pair ($2, $4), linenum ^ ":" ^ $6),
        (* if compare $6 "path" == 0 then "black" else *)
          (
            let a = Random.int 6 in
            let b = Random.int 256 in
            match a with
            | 0 -> Printf.sprintf "#00FF%02x" b
            | 1 -> Printf.sprintf "#00%02xFF" b
            | 2 -> Printf.sprintf "#FF00%02x" b
            | 3 -> Printf.sprintf "#%02x00FF" b
            | 4 -> Printf.sprintf "#FF%02x00" b
            | 5 -> Printf.sprintf "#%02xFF00" b
            | _ -> raise (Failure "random color generation")
          )
      )
    }
  | LPAREN node COMMA node COMMA qstring COMMA qstring RPAREN
    {
      let startpos = Parsing.symbol_start_pos() in
      let linenum = string_of_int startpos.pos_lnum in
      PipeGraph.Pair(PipeGraph.Pair(PipeGraph.Pair ($2, $4),
        linenum ^ ":" ^ $6), $8)
    };

nodelist:
  LBRACKET nodes RBRACKET {$2};

nodes:
  | nodes SEMICOLON node {$1 @ [$3]}
  | node {[$1]};

node:
  | LPAREN str COMMA LPAREN string_or_int COMMA string_or_int RPAREN RPAREN
    {PipeGraph.Pair ($2, PipeGraph.Pair ($5, $7))};
  | LPAREN str COMMA string_or_int RPAREN
    {PipeGraph.Pair ($2, PipeGraph.Pair (PipeGraph.SoICoreID $2, $4))};

string_or_int:
  | string_or_int PLUS string_or_int {PipeGraph.SoISum ($1, $3)}
  | str {PipeGraph.SoIString $1}
  | INT {PipeGraph.SoIInt $1}
  | COREID str {PipeGraph.SoICoreID $2};
