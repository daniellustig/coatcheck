{
  open Parser
  open Util
}
rule token = parse
  | "PTAG_OF_APIC"                  {APIC_PA}
  | "PTE_PA"                        {PTE_PA}
  | "PTAG_OF_PTE_FOR_VTAG"          {PTE_PA}
  | "PTE"                           {PTE}
  | "VA"                            {VA}
  | "PA"                            {PA}
  | "VTAG"                          {VTAG}
  | "PTAG"                          {PTAG}
  | "Data"                          {DATA}
  | "Status"                        {STATUS}
  | "acc"                           {ACC}
  | "dirty"                         {DIRTY}
  | "!"                             {NOT}
  | "?"                             {QUESTION}
  | "Read"                          {READ}
  | "Write"                         {WRITE}
  | "RMWRead"                       {RMWREAD}
  | "RMWWrite"                      {RMWWRITE}
  | "Fence"                         {FENCE}
  | "Initial"                       {INITIAL}
  | "Thread"                        {MICROOPS}
  | "Microops"                      {MICROOPS}
  | "Final"                         {FINAL}
  | "Forbidden"                     {FORBID}
  | "Permitted"                     {PERMIT}
  | "Required"                      {REQUIRED}
  | "Unobserved"                    {UNOBSERVED}
  | "Alternative"                   {ALTERNATIVE}
  | "Relationship"                  {RELATIONSHIP}
  | "("                             {LPAREN}
  | ")"                             {RPAREN}
  | "="                             {EQUALS}
  | "->"                            {RARROW}
  | [' ' '\t']                      {token lexbuf}
  | ['\n']
    {let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- { pos with
        Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
        Lexing.pos_bol = pos.Lexing.pos_cnum};
        EOL}
  | ['0'-'9']+ as i                 {INT(int_of_string(i))}
  | ['A'-'Z''a'-'z''0'-'9''_']+ as s {STRING(s)}
