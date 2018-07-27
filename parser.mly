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
    along with Qtpi in the file LICENSE; if not, write to the Free Software
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
  open Sourcepos
  open Instance
  
  exception ParserCrash of string
  
  let get_sourcepos() =
    Parsing.symbol_start_pos(), Parsing.symbol_end_pos()
  
  let bad s = raise (Program.ParseError(get_sourcepos(),s))

  let adorn inst = Instance.adorn (get_sourcepos()) inst
  
  let eadorn inst = Instance.adorn (get_sourcepos()) (ewrap None inst)
  
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
%token <string> STRING 
%token <char> CHAR 

%token EOP 
%token GIVEN
%token LPAR RPAR LBRACE RBRACE LSQPAR RSQPAR BAR GPLUS COLON EQUALS
%token IF THEN ELSE ELIF FI
%token INTTYPE BOOLTYPE CHARTYPE STRINGTYPE UNITTYPE QBITTYPE CHANTYPE BITTYPE LISTTYPE TYPEARROW PRIME
%token DOT DOTDOT
%token HADAMARD PHI CNOT I X NEWDEC QBITDEC LETDEC
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

%type  <(Name.name Instance.instance * Type._type) list * Processdef.processdef list> program
%type  <Type._type> readtype

%%
program: library processdefs EOP        {$1,$2}

library:
  | GIVEN typednames                    {$2}
  |                                     {[]}

typednames:
  | name COLON typespec                 {[adorn $1,$3]}
  | name COLON typespec COMMA typednames 
                                        {(adorn $1,$3)::$5}
                                        
processdefs:
  | processdef                          {[$1]}
  | processdef processdefs              {$1::$2}

processdef:
  procname LPAR params RPAR EQUALS ubprocess  
                                        {Processdef($1,$3,$6)}

procname:
  | name                                {adorn $1}
params:
  |                                     {[]}
  | paramseq                            {$1}
  
paramseq:
  | param                               {[$1]}
  | param COMMA paramseq                {$1::$3}
  
param:
  | name COLON typespec                 {adorn ($1,ref (Some $3))}
  | name                                {adorn ($1,ref None)}

name:
  NAME                                  {$1}
  
typespec:
  | func_typespec                       {$1}
  | typespec PROCESS                    {adorn (Process (Type.relist $1))}

func_typespec:
  | chan_typespec                       {$1}
  | chan_typespec TYPEARROW func_typespec    
                                        {adorn (Fun ($1,$3))}
  
chan_typespec:
  | tuple_typespec                      {$1}
  | CHANTYPE tuple_typespec             {adorn (Channel $2)}
  
tuple_typespec:
  | simple_typespec                     {$1}
  | simple_typespec STAR simple_typespecs
                                        {adorn (Tuple ($1::$3))}        
    
simple_typespec:
  | INTTYPE                             {adorn Int}
  | BOOLTYPE                            {adorn Bool}
  | CHARTYPE                            {adorn Char}
  | STRINGTYPE                          {adorn String}
  | BITTYPE                             {adorn Bit}
  | UNITTYPE                            {adorn Unit}
  | QBITTYPE                            {adorn Qbit}
  | typevar                             {adorn (TypeVar ($1))}
  | INT DOTDOT INT                      {let low = int_of_string $1 in
                                         let high = int_of_string $3 in
                                         if low<=high then adorn (Range (low,high))
                                         else raise (ParseError (get_sourcepos(), "low>high in range type"))
                                        } 
  | LPAR typespec RPAR                  {$2}
  | FORALL typevars DOT typespec        {adorn (Univ ($2,$4))}
  | simple_typespec LISTTYPE            {adorn (List ($1))}
  
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
  | TERMINATE                           {adorn Terminate}
  | procname primary                    {adorn (Call ($1,match $2.inst.enode with 
                                                         | EUnit     -> []
                                                         | ETuple es -> es
                                                         | _         -> [$2]
                                                     )
                                               )
                                        }
  | LPAR NEWDEC paramseq RPAR process   {adorn (WithNew ($3,$5))}
  | LPAR QBITDEC qspecs RPAR process    {adorn (WithQbit ($3,$5))}
  | LPAR LETDEC letspec RPAR process    {adorn (WithLet ($3,$5))}
  | qstep DOT process                   {adorn (WithQstep ($1,$3))}
  | gsum                                {adorn (GSum $1)}
  | LPAR ubprocess RPAR                 {$2}
  | IF ubif FI                          {$2}

ubif: 
  | expr THEN ubprocess ELSE ubprocess  {adorn (Cond ($1, $3, $5))}
  | expr THEN ubprocess ELIF ubif       {adorn (Cond ($1, $3, $5))}
  
ubprocess:
  | processpar                          {adorn (Par $1)} /* only case in which a process can be unbracketed */
  | process                             {$1}
  
processpar:
  | process                             {[$1]}
  | process BAR processpar              {$1::$3}

gsum:
  | iostep DOT process                  {[$1,$3]}
  | iostep DOT process GPLUS gsum       {($1,$3)::$5}
qspecs:
  | qspec                               {[$1]}
  | qspec COMMA qspecs                  {$1::$3}

qspec:
  | param                               {$1, None}
  | param EQUALS ntexpr                 {$1, Some $3}
  
letspec:
  | name EQUALS expr                    {adorn ($1, ref None     ), $3}
  | name COLON typespec EQUALS expr     {adorn ($1, ref (Some $3)), $5}
  
iostep:
  | expr QUERY LPAR paramseq RPAR       {adorn (Read ($1,$4))}
  | expr BANG ntexprs                   {let es = match $3 with 
                                                  | [{inst={enode=ETuple es}}] -> es
                                                  | es                         -> es
                                         in
                                         adorn (Write ($1,es))
                                        }

qstep:
  | expr MEASURE LPAR param RPAR        {adorn (Measure ($1,$4))}
  | ntexprs THROUGH expr                {adorn (Ugatestep ($1,$3))}

args:
  |                                     {[]}
  | ntexprs                             {$1}

primary:
  | LPAR RPAR                           {eadorn EUnit}
  | name                                {eadorn (EVar $1)}
  | BIT0                                {eadorn (EBit false)}
  | BIT1                                {eadorn (EBit true)}
  | INT                                 {eadorn (EInt (int_of_string $1))}
  | TRUE                                {eadorn (EBool (true))}
  | FALSE                               {eadorn (EBool (false))}
  | CHAR                                {eadorn (EChar $1)}
  | STRING                              {eadorn (EString $1)}
  | VZERO                               {eadorn (EBasisv BVzero) }
  | VONE                                {eadorn (EBasisv BVone )  }
  | VPLUS                               {eadorn (EBasisv BVplus) }
  | VMINUS                              {eadorn (EBasisv BVminus) }
  | ugate                               {eadorn (EGate $1)}
  | LSQPAR exprlist RSQPAR              {eadorn (EList $2)}
  | LPAR ntexprs RPAR                   {match $2 with
                                         | [e] -> e
                                         | es  -> eadorn (ETuple es)
                                        }
  | IF eif FI                           {eadorn($2.inst.enode)}
  
eif:
  | expr THEN expr ELSE expr            {eadorn (ECond ($1,$3,$5))}
  | expr THEN expr ELIF eif             {eadorn (ECond ($1,$3,$5))}
  
expr:
  | ntexpr                              {$1}
  | ntexpr COMMA ntexprs                {eadorn (ETuple ($1::$3))}

ntexprs:
  | ntexpr                              {[$1]}
  | ntexpr COMMA ntexprs                {$1::$3}

ntexpr:  /* a non-tuple expression */
  | primary                             {$1} 
  | app                                 {$1}
  | MINUS primary                       {eadorn (EMinus ($2))}
  | ntexpr PLUSPLUS ntexpr              {eadorn (EBitCombine ($1,$3))}
  | ntexpr APPEND primary               {eadorn (EAppend ($1,$3))}
  | arith                               {let e1,op,e2 = $1 in eadorn (EArith (e1,op,e2))}
  | compare                             {let e1,op,e2 = $1 in eadorn (ECompare (e1,op,e2))}
  | bool                                {let e1,op,e2 = $1 in eadorn (EBoolArith (e1,op,e2))}

app:
  | primary primary                     {eadorn (EApp ($1,$2))}
  | app primary                         {eadorn (EApp ($1,$2))}
  
arith:
  | ntexpr PLUS ntexpr                  {$1,Plus,$3}
  | ntexpr MINUS ntexpr                 {$1,Minus,$3}
  
compare:
  | ntexpr EQUALS ntexpr                {$1,Eq,$3}
  | ntexpr NOTEQUAL ntexpr              {$1,Neq,$3}

bool:
  | ntexpr AND ntexpr                   {$1,And,$3}
  | ntexpr OR ntexpr                    {$1,Or,$3}
  
ugate: 
  | HADAMARD                            {adorn GH}
  | CNOT                                {adorn GCnot}
  | I                                   {adorn GI}
  | X                                   {adorn GX}
  | PHI LPAR expr RPAR                  {adorn (GPhi ($3))}

exprlist:
  |                                     {[]}
  | expr                                {[$1]}
  | expr SEMICOLON exprlist             {$1::$3}

names:
  | name                                {[$1]}
  | name COMMA names                    {$1::$3}
  
/* entry point for reading types to save brain when defining contexts */

readtype:
  | typespec EOP                       {$1}

%%
