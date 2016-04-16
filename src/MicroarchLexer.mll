{
  open MicroarchParser
  open Util
  exception EoF
}
rule token = parse
  | "DefineMacro"                   {DEFINEMACRO}
  | "ExpandMacro"                   {EXPANDMACRO}
  | "StageName"                     {STAGENAME}
  | "Axiom"                         {AXIOM}
  | "microop"                       {MICROOP}
  | "microops"                      {MICROOP}
  | "core"                          {CORE}
  | "cores"                         {CORE}
  | "CoreOf"                        {COREID}
  | "thread"                        {THREAD}
  | "threads"                       {THREAD}
  | "Read"                          {READ}
  | "Write"                         {WRITE}
  | "RMWRead"                       {RMWREAD}
  | "RMWWrite"                      {RMWWRITE}
  | "Accessed"                      {ACCESSED}
  | "NotAccessed"                   {NOTACCESSED}
  | "AccessedDontCare"              {ACCESSEDDONTCARE}
  | "Dirty"                         {DIRTY}
  | "NotDirty"                      {NOTDIRTY}
  | "Clean"                         {NOTDIRTY}
  | "DirtyDontCare"                 {DIRTYDONTCARE}
  | "Fence"                         {FENCE}
  | "forall"                        {FORALL}
  | "exists"                        {EXISTS}
  | "with"                          {WITH}
  | "as"                            {AS}
  | ","                             {COMMA}
  | "."                             {PERIOD}
  | ":"                             {COLON}
  | ";"                             {SEMICOLON}
  | "/\\"                           {AND}
  | "\\/"                           {OR}
  | "~"                             {NOT}
  | "=>"                            {IMPLIES}
  | "<=>"                           {IFF}
  | "("                             {LPAREN}
  | ")"                             {RPAREN}
  | "["                             {LBRACKET}
  | "]"                             {RBRACKET}
  | '"'                             {QUOTE}
  | "+"                             {PLUS}
  | '%' [^ '\n']*                   {token lexbuf}
  | ['\n']
    {let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- { pos with
        Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
        Lexing.pos_bol = pos.Lexing.pos_cnum};
        token lexbuf}
  | ['\n' ' ' '\t']                 {token lexbuf}
  | ['0'-'9']+ as i                 {INT(int_of_string(i))}
  | ['A'-'Z''a'-'z''0'-'9''\'''/''_''-''#']+ as s {STRING(s)}
  | eof                             {EOF}

