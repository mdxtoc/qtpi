(*
    Copyright (C) 2018 Richard Bornat
     
        richard@bornat.me.uk

    This file is part of Qtpi, an interpreter for Gay and Nagarajan's CQP.

    Qtpi is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    Qtpi is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Qtpi in the file LICENSE; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*)
 
{
  open Parser
  
  exception LexError of Sourcepos.sourcepos * string
    
  let inc_linenum lexbuf =
    let curr = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- 
        { lexbuf.Lexing.lex_curr_p with Lexing.pos_lnum = curr.Lexing.pos_lnum+1;
                                        Lexing.pos_bol = curr.Lexing.pos_cnum
        }
  
  let get_linenum lexbuf = 
    let curr = lexbuf.Lexing.lex_curr_p in
    curr.Lexing.pos_lnum
    
  let get_loc lexbuf =
    (!Parserparams.filename, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)

  let backslashed = function
    | 'n' -> '\n'
    | 'r' -> '\r'
    | 'b' -> '\r'
    | 't' -> '\t'
    | c   -> c

  let stringbuffer = Buffer.create 256
}

let BLANK = [' ' '\t']
let NEWLINE = '\n' | "\r\n"

let DIGIT = ['0'-'9']
let ALPHA =  ['a'-'z'] | ['A'-'Z']
let ALPHANUM = ALPHA | DIGIT | '_' 

let number = DIGIT+ ('.' DIGIT+)? (['e' 'E'] '-'? DIGIT+ )?

let name   = ALPHA (ALPHA | DIGIT | '_' | '\'')*

let tvname = '\'' (name | '\'' name | '^' name | '*' name)

let tpnum = DIGIT+ ('.' DIGIT+)*

rule make_token = parse

  | BLANK       { make_token lexbuf} (* Skip blanks and tabs *)
  | NEWLINE     { inc_linenum lexbuf; make_token lexbuf}
  | "(*"        { bracomment (get_loc lexbuf) lexbuf; make_token lexbuf }

  | eof         {EOP}   (* Give up on end of file *)

  | '('         {LPAR}
  | ')'         {RPAR}
  | '['         {LSQPAR}
  | ']'         {RSQPAR}
  | '|'         {PARSEP}
  | ':'         {COLON}
  | '='         {EQUALS}
  | '*'         {STAR}
  | "><"        {TENSORP}
  
  | "true"      {TRUE}
  | "false"     {FALSE}
  
  | "if"        {IF}
  | "then"      {THEN}
  | "else"      {ELSE}
  | "elif"      {ELIF}
  | "elsf"      {ELIF}
  | "fi"        {FI}
    
  | "num"       {NUMTYPE}
  | "bool"      {BOOLTYPE}
  | "bit"       {BITTYPE}
  | "gate"      {GATETYPE}
  | "qbit"      {QBITTYPE}
  | "qstate"    {QSTATETYPE}
  | "^"         {CHANTYPE}
  | "char"      {CHARTYPE}
  | "string"    {STRINGTYPE}
  
  | '.'         {DOT}
  | ".."        {DOTDOT}
    
  | "new"       {NEWDEC}
  | "untraced"  {UNTRACED}
  | "newq"      {QBITDEC}
  | "let"       {LETDEC}
  | "match"     {MATCH}
  
  | "fun"       {FUN}
  | "proc"      {PROC}
  | "with"      {WITH}
  | "where"     {WHERE}
  | "lam"       {LAMBDA}
  | "/^"        {TESTPOINT}
  | ".*"        {PROCITER}
  
  | '?'         {QUERY}
  | '!'         {BANG}
  | "-/-"       {MEASURE}
  | ">>"        {THROUGH}
  
  | ','         {COMMA}
  | ';'         {SEMICOLON}
  
  | '+'         {PLUS}
  | '-'         {MINUS}
  | '/'         {DIV}
  | '%'         {MOD}
  (* and STAR as multiply *)
  | "**"        {POW}
    
  | "|0>"       {VZERO}
  | "|1>"       {VONE}
  | "|+>"       {VPLUS}
  | "|->"       {VMINUS}
  
  | '='         {EQUALS}
  | "<>"        {NOTEQUAL}
  | '<'         {LESS}
  | "<="        {LESSEQUAL}
  | ">="        {GREATEREQUAL}
  | '>'         {GREATER}
  
  | "&&"        {AND}
  | "||"        {OR}
  | "not"       {NOT}
  
  | '@'         {APPEND}
  | "::"        {CONS}
      
  | '_'         {UNDERSCORE}
  
  | "_0"        {TERMINATE}
  
  | "0b0"       {BIT0}
  | "0b1"       {BIT1}
  
  | "All"       {FORALL}
  | "process"   {PROCESS}
  
  | "->"        {TYPEARROW}
    
  | "'" [^ '\\' '\'' 'n' '\r' '\t' ] "'"
                {CHAR(Lexing.lexeme_char lexbuf 1)}
  | "'\\" ['\\' '\'' '"' 'n' 't' 'b' 'r' ' '] "'"
                { CHAR(backslashed (Lexing.lexeme_char lexbuf 2)) }
  | "'\\" _
                { let l = Lexing.lexeme lexbuf in
                  let esc = String.sub l 1 (String.length l - 1) in
                  raise (LexError(get_loc lexbuf, ("illegal escape \\" ^ esc)))
                }

  | '"'         { Buffer.clear stringbuffer;
                  STRING (string (get_loc lexbuf) lexbuf)
                }

  | number      {NUM (Lexing.lexeme lexbuf)}
  | name        {NAME (Lexing.lexeme lexbuf)}   (* should be interned *)
  | tvname      {TVNAME (Lexing.lexeme lexbuf)} (* should be interned *)
  | tpnum       {TPNUM (Lexing.lexeme lexbuf)}
  
  | _           {raise (LexError (get_loc lexbuf, "Invalid character '" ^ 
                                                  Char.escaped (Lexing.lexeme_char lexbuf 0) ^ 
                                                  "'"
                                 )
                       )
                }

and bracomment spos = parse
    |   "(*"        { bracomment (get_loc lexbuf) lexbuf; 
                      bracomment spos lexbuf
                    }
    |   "*)"        { () }
    |   "\r\n"
    |   '\n'        { inc_linenum lexbuf; bracomment spos lexbuf }
    |   eof         { raise (LexError (spos, "unmatched comment-bracket '(*'")) }
    |   _           { bracomment spos lexbuf }
      
and string spos = parse
    | '"'                                       { Buffer.contents stringbuffer }
    | '\\' ['\\' '\'' '"' 'n' 't' 'b' 'r' ' ']  { let c = backslashed (Lexing.lexeme_char lexbuf 1) in
                                                  Buffer.add_char stringbuffer c; string spos lexbuf 
                                                }
    | eof                                       { raise (LexError (spos, "unterminated string")) }
    | _ as char                                 { Buffer.add_char stringbuffer char; string spos lexbuf }
 
{
  let build_prog_from_string s =
    Parser.program make_token (Lexing.from_string s)
}
