/*
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
    along with Qtpi; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*/

%{

  open Program
  open Processdef
  open Process
  open Step
  open Type
  open Name
  open Expr
  open Ugate
  open Sourcepos
  open Instance
  
  exception ParserCrash of string
  
  let get_sourcepos() =
    Parsing.symbol_start_pos(), Parsing.symbol_end_pos()
  
  let bad s = raise (Program.ParseError(get_sourcepos(),s))

  let adorn inst = Instance.adorn (get_sourcepos()) inst
  
(*let tripletadorn pre lab tof = Com.tripletadorn (get_sourcepos()) pre lab tof
  
  let simplecomadorn ipre c = Com.simplecomadorn (get_sourcepos()) ipre c
  
  let structcomadorn c = Com.structcomadorn (get_sourcepos()) c
  
  let intfadorn   i = Intfdesc.intfadorn (get_sourcepos()) i
  
  let stitchadorn o n spo a = Stitch.stitchadorn (get_sourcepos()) o n spo a
  
  let knotadorn k = Knot.knotadorn (get_sourcepos()) k  
 *)
 
(*  
  let warn s = report (Warning (get_sourcepos(), s))
  
 *)   
  (* let check_conditional_assign assign =
       match classify_assign true true assign with
       | LocbecomesEs (true,_) (*as a*) -> bad "store-conditional not supported. Sorry." (*; a*)
       | _                              -> bad ("conditional assignment must be store-conditional")
   *)
    
%}

%token LPAR RPAR

%token <string> INT
%token <string> NAME 

%token EOP 
%token GIVEN
%token LPAR RPAR LBRACE RBRACE LSQPAR RSQPAR BAR COLON EQUALS
%token IF THEN ELSE FI
%token INTTYPE BOOLTYPE UNITTYPE QBITTYPE CHANTYPE BITTYPE LISTTYPE TYPEARROW PRIME
%token DOT DOTDOT
%token HADAMARD PHI CNOT I X NEWDEC QBITDEC 
%token QUERY BANG MEASURE THROUGH 
%token PLUSPLUS PLUS MINUS
%token EQUALS NOTEQUAL
%token APPEND
%token AND OR
%token UNIT TERMINATE
%token COMMA STAR SEMICOLON
%token TRUE FALSE BIT0 BIT1
%token VZERO VONE VPLUS VMINUS

/* remember %left %right %nonassoc and increasing priority */
%left AND OR
%nonassoc EQUALS NOTEQ
%left PLUS MINUS
%left PLUSPLUS
%left APPEND

%right TYPEARROW
%nonassoc STAR

%start program             /* Entry point */

%token FORALL PROCESS
%start readtype

%type  <(Name.name * Type._type) list * Processdef.processdef list> program
%type  <Type._type> readtype

%%
program: library processdefs EOP        {$1,$2}

library:
  | GIVEN typednames                    {$2}
  |                                     {[]}

typednames:
  | name COLON typespec                 {[$1,$3]}
  | name COLON typespec COMMA typednames 
                                        {($1,$3)::$5}
                                        
processdefs:
  | processdef                          {[$1]}
  | processdef processdefs              {$1::$2}

processdef:
  name LPAR params RPAR EQUALS ubprocess  
                                        {Processdef($1,$3,$6)}

params:
  |                                     {[]}
  | paramseq                            {$1}
  
paramseq:
  | param                               {[$1]}
  | param COMMA paramseq                {$1::$3}
  
param:
  | name COLON typespec                 {$1,Some $3}
  | name                                {$1,None}

name:
  NAME                                  {$1}
  
typespec:
  | func_typespec                       {$1}
  | typespec PROCESS                    {Process (Type.relist $1)
                                        }

func_typespec:
  | chan_typespec                       {$1}
  | chan_typespec TYPEARROW func_typespec    
                                        {Fun ($1,$3)}
  
chan_typespec:
  | tuple_typespec                      {$1}
  | CHANTYPE tuple_typespec             {Channel $2}
  
tuple_typespec:
  | simple_typespec                     {$1}
  | simple_typespec STAR simple_typespecs
                                        {Tuple ($1::$3)}        
    
simple_typespec:
  | INTTYPE                             {Int}
  | BOOLTYPE                            {Bool}
  | BITTYPE                             {Bit}
  | UNITTYPE                            {Unit}
  | LPAR RPAR                           {Unit}
  | QBITTYPE                            {Qbit}
  | typevar                             {TypeVar ($1)}
  | INT DOTDOT INT                      {let low = int_of_string $1 in
                                         let high = int_of_string $3 in
                                         if low<=high then Range (low,high)
                                         else raise (ParseError (get_sourcepos(), "low>high in range type"))
                                        } 
  | LPAR typespec RPAR                  {$2}
  | FORALL typevars DOT typespec        {Univ ($2,$4)}
  | simple_typespec LISTTYPE            {List ($1)}
  
simple_typespecs:
  | simple_typespec                     {[$1]}
  | simple_typespec STAR simple_typespecs
                                        {$1::$3}
                                        
typevar:
  | PRIME name                          {$2}
  
typevars:
  | typevar                             {[$1]}
  | typevar COMMA typevars              {$1::$3}
  
process:
  | TERMINATE                           {Terminate}
  | name primary                        {Call ($1,match $2.inst with 
                                                  | EUnit     -> []
                                                  | ETuple es -> es
                                                  | _         -> [$2]
                                              )
                                        }
  | LPAR NEWDEC paramseq RPAR process   {WithNew ($3,$5)}
  | LPAR QBITDEC qspecs RPAR process     {WithQbit ($3,$5)}
  | step DOT process                    {WithStep ($1,$3)}
  | LPAR ubprocess RPAR                 {$2}
  | IF expr THEN ubprocess ELSE ubprocess FI
                                        {Cond ($2,$4,$6)}
ubprocess:
  | processpar                          {Par $1} /* only case in which a process can be unbracketed */
  | process                             {$1}
  
processpar:
  | process                             {[$1]}
  | process BAR processpar              {$1::$3}

qspecs:
  | qspec                               {[$1]}
  | qspec COMMA qspecs                  {$1::$3}

qspec:
  | NAME                                {$1, None}
  | NAME EQUALS vbasis                  {$1, Some $3}
  
vbasis:
  | VZERO                               {VZero}
  | VONE                                {VOne }
  | VPLUS                               {VPlus}
  | VMINUS                              {VMinus}
  
step:
  | expr QUERY LPAR paramseq RPAR       {Read ($1,$4)}
  | expr BANG ntexprs                   {let es = match $3 with 
                                                  | [{inst=ETuple es}] -> es
                                                  | es                 -> es
                                         in
                                         Write ($1,es)
                                        }
  | expr MEASURE LPAR param RPAR        {Measure ($1,$4)}
  | ntexprs THROUGH ugate               {Ugatestep ($1,$3)}
  /* | LBRACE expr RBRACE                  {Eval $2} */

args:
  |                                     {[]}
  | ntexprs                             {$1}

primary:
  | LPAR RPAR                           {adorn EUnit}
  | name                                {adorn (EVar $1)}
  | BIT0                                {adorn (EBit false)}
  | BIT1                                {adorn (EBit true)}
  | INT                                 {adorn (EInt (int_of_string $1))}
  | TRUE                                {adorn (EBool (true))}
  | FALSE                               {adorn (EBool (false))}
  | LSQPAR exprlist RSQPAR              {adorn (EList $2)}
  | LPAR ntexprs RPAR                   {match $2 with
                                         | [e] -> e
                                         | es  -> adorn (ETuple es)
                                        }
  | IF expr THEN expr ELSE expr FI      {adorn( ECond ($2,$4,$6))}
  
expr:
  | ntexpr                              {$1}
  | ntexpr COMMA ntexprs                {adorn (ETuple ($1::$3))}

ntexprs:
  | ntexpr                              {[$1]}
  | ntexpr COMMA ntexprs                {$1::$3}

ntexpr:  /* a non-tuple expression */
  | primary                             {$1} 
  | app                                 {$1}
  | MINUS primary                       {adorn (EMinus ($2))}
  | ntexpr PLUSPLUS ntexpr              {adorn (EBitCombine ($1,$3))}
  | ntexpr APPEND primary               {adorn (EAppend ($1,$3))}
  | arith                               {let e1,op,e2 = $1 in adorn (EArith (e1,op,e2))}
  | compare                             {let e1,op,e2 = $1 in adorn (ECompare (e1,op,e2))}
  | bool                                {let e1,op,e2 = $1 in adorn (EBoolArith (e1,op,e2))}

app:
  | primary primary                     {adorn (EApp ($1,$2))}
  | app primary                         {adorn (EApp ($1,$2))}
  
arith:
  | ntexpr PLUS ntexpr                      {$1,Plus,$3}
  | ntexpr MINUS ntexpr                     {$1,Minus,$3}
  
compare:
  | ntexpr EQUALS ntexpr                    {$1,Eq,$3}
  | ntexpr NOTEQUAL ntexpr                  {$1,Neq,$3}

bool:
  | ntexpr AND ntexpr                       {$1,And,$3}
  | ntexpr OR ntexpr                        {$1,Or,$3}
  
ugate: 
  | HADAMARD                            {GH}
  | CNOT                                {GCnot}
  | I                                   {GI}
  | X                                   {GX}
  | PHI LPAR expr RPAR                  {GPhi ($3)}
  | IF expr THEN ugate ELSE ugate FI    {GCond ($2,$4,$6)}

exprlist:
  |                                     {[]}
  | expr                                {[$1]}
  | expr SEMICOLON exprlist             {$1::$3}

names:
  | name                             {[$1]}
  | name COMMA names                  {$1::$3}
  
/* entry point for reading types to save brain when defining contexts */

readtype:
  | typespec EOP                       {$1}

%%
