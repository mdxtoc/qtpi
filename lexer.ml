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


open Parser
open Functionutils

exception LexError of Sourcepos.sourcepos * string

let string_of_token = function
    | WITH      -> "WITH"
    | WHERE     -> "WHERE"
    | UNTRACED  -> "UNTRACED"
    | UNIT      -> "UNIT"
    | UNDERSCORE -> "UNDERSCORE"
    | RIGHTARROW -> "RIGHTARROW"
    | TVNAME (s) -> "TVNAME(" ^ s ^ ")" 
    | TRUE      -> "TRUE"
    | TPNUM (s) -> "TPNUM(" ^ s ^ ")"
    | THROUGH   -> "THROUGH"
    | THROUGHS  -> "THROUGHS"
    | THEN      -> "THEN"
    | TESTPOINT -> "TESTPOINT"
    | TERMINATE -> "TERMINATE"
    | TENSORPROD -> "TENSORPROD"
    | TENSORPOWER -> "TENSORPOWER"
    | STRINGTYPE -> "STRINGTYPE"
    | STRING cs  -> "STRING\"" ^ (String.concat "" (List.map Utf8.string_of_uchar cs)) ^ "\""
    | STAR      -> "STAR"
    | SEMICOLON -> "SEMICOLON"
    | RSQPAR    -> "RSQPAR"
    | RPAR      -> "RPAR"
    | RBRACE    -> "RBRACE"
    | QUERY     -> "QUERY"
    | QSTATETYPE -> "QSTATETYPE"
    | QBITTYPE  -> "QBITTYPE"
    | QBITSTYPE -> "QBITSTYPE"
    | QBITDEC   -> "QBITDEC"
    | QBITSDEC  -> "QBITSDEC"
    | QBITSJOIN -> "QBITSJOIN"
    | QBITSSPLIT -> "QBITSSPLIT"
    | LEFTREPEAT -> "LEFTREPEAT"
    | RIGHTREPEAT -> "RIGHTREPEAT"
    | PROCESS   -> "PROCESS"
    | PROC      -> "PROC"
    | POW       -> "POW"
    | PLUS      -> "PLUS"
    | PARSEP    -> "PARSEP"
    | OR        -> "OR"
    | OFFSIDE   -> "OFFSIDE"
    | NUMTYPE   -> "NUMTYPE"
    | NUM (s)   -> "NUM(" ^ s ^ ")"
    | NOTEQUAL -> "NOTEQUAL"
    | NOT       -> "NOT"
    | NEWDEC    -> "NEWDEC"
    | NAME (s)  -> "NAME(" ^ s ^ ")"
    | MOD       -> "MOD"
    | MINUS     -> "MINUS"
    | MEASURE   -> "MEASURE"
    | MEASURES  -> "MEASURES"
    | MATRIXTYPE -> "MATRIXTYPE"
    | MATCH     -> "MATCH"
    | LSQPAR    -> "LSQPAR"
    | LPAR      -> "LPAR"
    | LETDEC    -> "LETDEC"
    | LESSEQUAL -> "LESSEQUAL"
    | LESS      -> "LESS"
    | LEFTARROW -> "LEFTARROW"
    | LBRACE    -> "LBRACE"
    | LAMBDA    -> "LAMBDA"
    | KETTYPE   -> "KETTYPE"
    | KET (s)   -> "KET(" ^ s ^ ")"
    | IF        -> "IF"
    | GREATEREQUAL -> "GREATEREQUAL"
    | GREATER   -> "GREATER"
    | GATETYPE  -> "GATETYPE"
    | FUN       -> "FUN"
    | FORALL    -> "FORALL"
    | FI        -> "FI"
    | FALSE     -> "FALSE"
    | EQUALS    -> "EQUALS"
    | EOP       -> "EOP"
    | ELSE      -> "ELSE"
    | ELIF      -> "ELIF"
    | DOTDOT    -> "DOTDOT"
    | DOT       -> "DOT"
    | DIV       -> "DIV"
    | CONS      -> "CONS"
    | COMMA     -> "COMMA"
    | COLON     -> "COLON"
    | CHARTYPE  -> "CHARTYPE"
    | CHAR (uc) -> "CHAR'" ^ Utf8.string_of_uchar uc ^ "'"
    | CHANTYPE  -> "CHANTYPE"
    | BRATYPE   -> "BRATYPE"
    | BRA (s)   -> "BRA(" ^ s ^ ")"
    | BOOLTYPE  -> "BOOLTYPE"
    | BITTYPE   -> "BITTYPE"
    | ANGLETYPE -> "ANGLETYPE"
    | BIT1      -> "BIT1"
    | BIT0      -> "BIT0"
    | PI        -> "PI"
    | BANG      -> "BANG"
    | APPEND    -> "APPEND"
    | AND       -> "AND"
    | DAGGER    -> "DAGGER"
    | SXNUMTYPE -> "SXNUMTYPE"
    | DOWNARROW -> "DOWNARROW"
    | RESSHOW   -> "RESSHOW"
    | RESCOMPARE -> "RESCOMPARE"
  
let get_linenum lexbuf = 
  let (_,start_p) = Sedlexing.lexing_positions lexbuf in
  start_p.Lexing.pos_lnum
  
let get_loc lexbuf : Lexing.position * Lexing.position =
  Sedlexing.lexing_positions lexbuf

let bkconvert lexeme = Array.sub lexeme 1 (Array.length lexeme - 2)

let string_of_lexeme = String.concat "" <.> List.map Utf8.string_of_uchar <.> Array.to_list

let _BLANK = [%sedlex.regexp? Chars " \t" ]
let _NEWLINE = [%sedlex.regexp? '\n' | "\r\n" ]

let _DIGIT = [%sedlex.regexp? '0'..'9' ]
let _ALPHA =  [%sedlex.regexp? 'a'..'z' | 'A'..'Z' ]
let _ALPHANUM = [%sedlex.regexp? _ALPHA | _DIGIT | '_' ]

let number = [%sedlex.regexp? Plus _DIGIT, Opt ('.', Plus _DIGIT), Opt (Chars"eE", Opt('-'), Plus _DIGIT) ]

let name   = [%sedlex.regexp? _ALPHA, Star (_ALPHA | _DIGIT | '_' | '\'') ]

let tvname = [%sedlex.regexp? '\'', Opt(Chars "\'^*"), name ]

let tpnum = [%sedlex.regexp? Plus _DIGIT, Star ('.', Plus _DIGIT) ]

let bke = [%sedlex.regexp? Chars "01+-" ]

let bra = [%sedlex.regexp? '<', Plus bke, '|' ]
let ket = [%sedlex.regexp? '|', Plus bke, '>' ]

let rec make_token : Sedlexing.lexbuf -> Parser.token = fun lexbuf ->
  match%sedlex lexbuf with
  | _BLANK      -> make_token lexbuf (* Skip blanks and tabs *)
  | _NEWLINE    -> make_token lexbuf (* it counts ... *)
  | "(*"        -> bracomment (get_loc lexbuf) lexbuf; make_token lexbuf 

  | eof         -> EOP   (* Give up on end of file *)

  | '('         -> LPAR
  | ')'         -> RPAR
  | '['         -> LSQPAR
  | ']'         -> RSQPAR
  | '|'         -> PARSEP
  | ':'         -> COLON
  | '='         -> EQUALS
  | '*'         -> STAR
  | "><"        -> TENSORPROD
  | 0x2297      -> TENSORPROD   (* ⊗ *)
  | "><><"      -> TENSORPOWER
  | 0x2297, 0x2297      
                -> TENSORPOWER  (* ⊗⊗ *)
  | "^^"        -> DAGGER
  | 0x2020      -> DAGGER       (* † *)
  | "true"      -> TRUE
  | "false"     -> FALSE
  
  | "if"        -> IF
  | "then"      -> THEN
  | "else"      -> ELSE
  | "elif"      -> ELIF
  | "elsf"      -> ELIF
  | "fi"        -> FI
    
  | "num"       -> NUMTYPE
  | "bool"      -> BOOLTYPE
  | "bit"       -> BITTYPE
  | "angle"     -> ANGLETYPE
  | "gate"      -> GATETYPE
  | "qbit"      -> QBITTYPE
  | "qbits"     -> QBITSTYPE
  | "qubit"     -> QBITTYPE
  | "qubits"    -> QBITSTYPE
  | "qstate"    -> QSTATETYPE
  | "qustate"   -> QSTATETYPE
  | "^"         -> CHANTYPE
  | "char"      -> CHARTYPE
  | "sxnum"     -> SXNUMTYPE
  | "string"    -> STRINGTYPE
  | "matrix"    -> MATRIXTYPE
  | "bra"       -> BRATYPE
  | "ket"       -> KETTYPE
  
  | '.'         -> DOT
  | ".."        -> DOTDOT
    
  | "new"       -> NEWDEC
  | "untraced"  -> UNTRACED
  | "newq"      -> QBITDEC
  | "newqs"     -> QBITSDEC
  | "joinqs"    -> QBITSJOIN
  | "splitqs"   -> QBITSSPLIT
  | "let"       -> LETDEC
  | "match"     -> MATCH
  
  | "fun"       -> FUN
  | "proc"      -> PROC
  | "with"      -> WITH
  | "where"     -> WHERE
  | "lam"       -> LAMBDA
  | 0x03bb      -> LAMBDA       (* λ *)
  | "/^"        -> TESTPOINT
  | 0x2041      -> TESTPOINT    (* ⁁ *)
  | "|:"        -> LEFTREPEAT   
  | ":|"        -> RIGHTREPEAT 
  | 0x1d106     -> LEFTREPEAT   (* 𝄆 *)
  | 0x1d107     -> RIGHTREPEAT  (* 𝄇 *)
  | '?'         -> QUERY
  | '!'         -> BANG
  | "-/-"       -> MEASURE
  | "-//-"      -> MEASURES
  | 0x2322, 0x0338
                -> MEASURE       (* ⌢̸ *)
  | 0x2322, 0x20EB
                -> MEASURES      (* ⌢⃫ *)
  | ">>"        -> THROUGH
  | ">>>"       -> THROUGHS
  
  | ','         -> COMMA
  | ';'         -> SEMICOLON
  
  | '+'         -> PLUS
  | '-'         -> MINUS
  | '/'         -> DIV
  | '%'         -> MOD
  (* and STAR as multiply *)
  | "**"        -> POW
    
  | '='         -> EQUALS
  | "<>"        -> NOTEQUAL
  | '<'         -> LESS
  | "<="        -> LESSEQUAL
  | ">="        -> GREATEREQUAL
  | '>'         -> GREATER
  
  | "&&"        -> AND
  | "||"        -> OR
  | "not"       -> NOT
  | 0x00ac      -> NOT          (* ¬ *)
  
  | '@'         -> APPEND
  | "::"        -> CONS
      
  | '_'         -> UNDERSCORE
  
  | "_0"        -> TERMINATE
  
  | "0b0"       -> BIT0
  | "0b1"       -> BIT1
  
  | 0x1d745     -> PI               (* 𝝅 *)
  
  | "All"       -> FORALL
  | "process"   -> PROCESS
  
  | "<-"        -> LEFTARROW
  | 0x2190      -> LEFTARROW        (* ← *)

  | "->"        -> RIGHTARROW
  | 0x2192      -> RIGHTARROW       (* → *)
  
  | 0x2193      -> DOWNARROW        (* ↓ *)
  
  | "show"      -> RESSHOW
  | "compare"   -> RESCOMPARE
    
  | "'", Compl (Chars "'\\\n\r\t"), "'"
                -> CHAR (Sedlexing.lexeme_char lexbuf 1)
  | "'\\", Chars "\\'\"ntbr ", "'"
                ->  CHAR(Utf8.unescaped (Sedlexing.lexeme_char lexbuf 2)) 
  | "'\\", any  ->  raise (LexError(get_loc lexbuf, Printf.sprintf "illegal escape \\%s" (Utf8.string_of_uchar (Sedlexing.lexeme_char lexbuf 2))))
  | '"'         ->  STRING (string [] (get_loc lexbuf) lexbuf)
                

  | number      -> NUM (string_of_lexeme (Sedlexing.lexeme lexbuf))
  | name        -> NAME (string_of_lexeme (Sedlexing.lexeme lexbuf))   (* should be interned *)
  | tvname      -> TVNAME (string_of_lexeme (Sedlexing.lexeme lexbuf)) (* should be interned *)
  | tpnum       -> TPNUM (string_of_lexeme (Sedlexing.lexeme lexbuf))
  
  | bra         -> BRA (string_of_lexeme (bkconvert (Sedlexing.lexeme lexbuf)))
  | ket         -> KET (string_of_lexeme (bkconvert (Sedlexing.lexeme lexbuf)))

  | any         -> raise (LexError (get_loc lexbuf, Printf.sprintf "Invalid character '%s'"
                                                                (Utf8.escaped (Sedlexing.lexeme_char lexbuf 0))
                                   )
                         )
  | _           -> raise (Settings.Can'tHappen "bottom of Lexer.make_token")
  
and bracomment spos lexbuf = 
    match%sedlex lexbuf with
    |   "(*"        ->  bracomment (get_loc lexbuf) lexbuf; 
                        bracomment spos lexbuf
    |   "*)"        ->  () 
    |   _NEWLINE    ->  bracomment spos lexbuf 
    |   eof         ->  raise (LexError (spos, "unmatched comment-bracket '(*'")) 
    |   any         ->  bracomment spos lexbuf 
    | _             -> raise (Settings.Can'tHappen "bottom of Lexer.bracomment")
  
      
and string cs spos lexbuf = 
    match%sedlex lexbuf with
    | '"'                       ->  List.rev cs
    | '\\', Chars "\\'\"ntbr "  ->  let c = Utf8.unescaped (Sedlexing.lexeme_char lexbuf 1) in
                                    string (c::cs) spos lexbuf 
                                                
    | eof                       ->  raise (LexError (spos, "unterminated string")) 
    | any                       ->  string (Sedlexing.lexeme_char lexbuf 0::cs) spos lexbuf 
    | _                         ->  raise (Settings.Can'tHappen "bottom of Lexer.string")
 
(* let build_prog_from_string s =
    Parser.program make_token (Lexing.from_string s) *)
