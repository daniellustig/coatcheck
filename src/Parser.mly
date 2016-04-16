%token <int> INT
%token <string> STRING
%token APIC_PA PTE_PA
%token DATA PTE STATUS
%token VA PA VTAG PTAG
%token ACC DIRTY NOT
%token READ WRITE RMWREAD RMWWRITE FENCE
%token INITIAL MICROOPS FINAL
%token FORBID PERMIT REQUIRED UNOBSERVED
%token RELATIONSHIP ALTERNATIVE
%token LPAREN RPAREN
%token EQUALS RARROW
%token QUESTION
%token EOL
%start main
%type <PipeGraph.expectedResult * PipeGraph.boundaryCondition list * ((((PipeGraph.microop list, PipeGraph.architectureLevelEdge list) PipeGraph.prod, PipeGraph.boundaryCondition list) PipeGraph.prod) list)> main
%%
main:

initial programs outcome {($3, $1, $2)};

initial:
  | INITIAL EOL conditions {$3}
  | conditions {$1};

conditions:
  | conditions condition {$1 @ [$2]}
  | {[]};

condition:
  pa EQUALS data EOL {PipeGraph.Pair ($1, $3)};

va:
  LPAREN VA INT INT RPAREN {{PipeGraph.vtag=$3; PipeGraph.vindex=$4}};

pa:
  LPAREN PA ptag INT RPAREN {{PipeGraph.ptag=$3; PipeGraph.pindex=$4}}

ptag:
  | INT {PipeGraph.PTag ($1)};
  | LPAREN PTE_PA INT RPAREN {PipeGraph.PTETag ($3)}
  | LPAREN APIC_PA STRING INT RPAREN
    {PipeGraph.APICTag ($3, $4)}

data:
  | INT {PipeGraph.NormalData ($1)}
  | LPAREN DATA INT RPAREN {PipeGraph.NormalData ($3)}
  | LPAREN DATA QUESTION RPAREN {PipeGraph.UnknownData}
  | LPAREN DATA STRING INT RPAREN {PipeGraph.OtherData ($3, $4)}
  | LPAREN PTE INT ptag status RPAREN {PipeGraph.PageTableEntry ($3, $4, $5)};
  | LPAREN PTE VTAG INT RARROW PTAG ptag status RPAREN
    {PipeGraph.PageTableEntry ($4, $7, $8)};

status:
  | LPAREN STATUS acc dirty RPAREN {{PipeGraph.accessed=$3; PipeGraph.dirty=$4}}
  | acc dirty {{PipeGraph.accessed=$1; PipeGraph.dirty=$2}};

acc:
  | ACC {true}
  | NOT ACC {false};

dirty:
  | DIRTY {true}
  | NOT DIRTY {false};

programs:
  | programs ALTERNATIVE EOL program {$1 @ [$4]}
  | program {[$1]};
  | ALTERNATIVE EOL program {[$3]};

program:
  | program FINAL EOL {$1}
  | program MICROOPS EOL {$1}
  | program microop
    {let PipeGraph.Pair (PipeGraph.Pair (a1, a2), a3) = $1 in
      PipeGraph.Pair (PipeGraph.Pair (a1 @ [$2], a2), a3)}
  | program relationship
    {let PipeGraph.Pair (PipeGraph.Pair (a1, a2), a3) = $1 in
      PipeGraph.Pair (PipeGraph.Pair (a1, a2 @ [$2]), a3)}
  | program condition
    {let PipeGraph.Pair (PipeGraph.Pair (a1, a2), a3) = $1 in
      PipeGraph.Pair (PipeGraph.Pair (a1, a2), a3 @ [$2])}
  | microop {PipeGraph.Pair (PipeGraph.Pair ([$1], []), [])}
  | relationship {PipeGraph.Pair (PipeGraph.Pair ([], [$1]), [])}
  | condition {PipeGraph.Pair (PipeGraph.Pair ([], []), [$1])}
  | MICROOPS EOL {PipeGraph.Pair (PipeGraph.Pair ([], []), [])}

relationship:
  RELATIONSHIP STRING INT INT RARROW INT INT EOL
  {PipeGraph.Pair(PipeGraph.Pair($3, $6), $2)};

microop:
  | INT INT INT access EOL {print_endline "Warning: using old .test format; assuming coreID=given number, threadID=0"; {PipeGraph.globalID=$1; PipeGraph.coreID=$2; PipeGraph.threadID0=0; PipeGraph.intraInstructionID0=$3; PipeGraph.access=$4}};
  | INT INT INT INT access EOL {{PipeGraph.globalID=$1; PipeGraph.coreID=$2; PipeGraph.threadID0=$3; PipeGraph.intraInstructionID0=$4; PipeGraph.access=$5}};

access:
  | LPAREN READ va pa data RPAREN {PipeGraph.Read ([], $3, $4, $5)}
  | LPAREN WRITE va pa data RPAREN {PipeGraph.Write ([], $3, $4, $5)}
  | LPAREN RMWREAD va pa data RPAREN {PipeGraph.Read (["RMW"], $3, $4, $5)}
  | LPAREN RMWWRITE va pa data RPAREN {PipeGraph.Write (["RMW"], $3, $4, $5)}
  | LPAREN READ types va pa data RPAREN {PipeGraph.Read ($3, $4, $5, $6)}
  | LPAREN WRITE types va pa data RPAREN {PipeGraph.Write ($3, $4, $5, $6)}
  | LPAREN FENCE types RPAREN {PipeGraph.Fence ($3)}
  | LPAREN FENCE types va RPAREN {PipeGraph.FenceVA ($3, $4)};

types:
  | types STRING { if compare $2 "normal" == 0 then $1 else $1 @ [$2] }
  | STRING { [$1] }

outcome:
  | PERMIT {PipeGraph.Permitted}
  | FORBID {PipeGraph.Forbidden}
  | UNOBSERVED {PipeGraph.Unobserved}
  | REQUIRED {PipeGraph.Required};
