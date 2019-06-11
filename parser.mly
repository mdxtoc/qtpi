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
  open Parserparams
  open Program
  open Def
  open Process
  open Step
  open Type
  open Name
  open Expr
  open Basisv
  open Pattern
  open Sourcepos
  open Instance
  
  exception ParserCrash of string
  
  let get_sourcepos() =
    !Parserparams.filename, Parsing.symbol_start_pos(), Parsing.symbol_end_pos()
  
  let bad s = raise (Program.ParseError(get_sourcepos(),s))

  let adorn inst = Instance.adorn (get_sourcepos()) inst
  
  let eadorn inst = Instance.adorn (get_sourcepos()) (ewrap None inst)
  
  let padorn inst = Instance.adorn (get_sourcepos()) (pwrap None inst)
     
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

%token <string> NUM
%token <string> NAME 
%token <string> TVNAME 
%token <string> STRING 
%token <char> CHAR 

%token EOP OFFSIDE /* could it be EOP? No. */
%token FUN PROC WHERE LAMBDA WITH
%token LPAR RPAR LBRACE RBRACE LSQPAR RSQPAR PARSEP COLON EQUALS
%token IF THEN ELSE ELIF FI
%token NUMTYPE BOOLTYPE CHARTYPE STRINGTYPE UNITTYPE GATETYPE QBITTYPE QSTATETYPE CHANTYPE BITTYPE LISTTYPE TYPEARROW
%token DOT DOTDOT UNDERSCORE
%token NEWDEC QBITDEC LETDEC MATCH 
%token QUERY BANG MEASURE THROUGH 
%token PLUS MINUS DIV MOD TENSORP
%token EQUALS NOTEQUAL LESSEQUAL LESS GREATEREQUAL GREATER
%token APPEND CONS
%token AND OR NOT
%token UNIT TERMINATE
%token COMMA STAR SEMICOLON
%token TRUE FALSE BIT0 BIT1
%token VZERO VONE VPLUS VMINUS
%token FORALL PROCESS

/* remember %left %right %nonassoc and increasing priority */
/* %left WHERE */
%nonassoc LAMBDA
%nonassoc COMMA
%right CONS
%left AND OR
%right NOT
%nonassoc EQUALS NOTEQUAL LESSEQUAL LESS GREATEREQUAL GREATER
%left PLUS MINUS
%left mult_op STAR DIV MOD
%left TENSORP
%left APPEND

%right TYPEARROW
/* %nonassoc STAR */

%start program             /* Entry point */
%start readtype
%start readexpr

%type  <Def.def list> program
%type  <Type._type> readtype
%type  <Expr.expr> readexpr

%%
indentPrev:                             
 |                                      {push_offsideline Parserparams.Prev}
  
indentHere:                             
 |                                      {push_offsideline Parserparams.Here}
  
indentNext:                             
 |                                      {push_offsideline Parserparams.Next}
  
outdent:    
  | OFFSIDE                             {pop_offsideline ()}
  |                                     {pop_offsideline ()}
  
program: defs EOP                       {$1}
                                        
defs:
  | def                                 {[$1]}
  | def defs                            {$1::$2}

def:
  | processdef                          {$1}
  | functiondefs                        {$1}
  | letdef                              {$1}
  
processdef:
  PROC procname LPAR procparams RPAR EQUALS processbody  
                                        {Processdef($2,$4,$7)}

processbody:
  | process                             {$1, None}
  | process WITH monitor                {$1, Some $3}

monitor:
  | process                             {$1} /* for now */
  
procname:
  | name                                {adorn $1}

procparams:
  |                                     {[]}
  | paramseq                            {$1}
  
paramseq:
  | param                               {[$1]}
  | param COMMA paramseq                {$1::$3}
  
param:
  | name COLON typespec                 {adorn ($1,ref (Some $3))}
  | name                                {adorn ($1,ref None)}

functiondefs:
  FUN fdefs                             {Functiondefs $2}
  
fdefs:
  | fdef                                {[$1]}
  | fdef fdefs                          {$1::$2}

fdef:
  funname fparams restypeopt EQUALS indentNext expr outdent    
                                        {let rt = ref $3 in ($1,$2,rt,$6)}
  
funname:
  name                                  {adorn $1}
  
fparam:
  | name                                {padorn (PatName $1)}
  | UNDERSCORE                          {padorn PatAny}
  | LPAR RPAR                           {padorn PatUnit}
  | LPAR bpattern RPAR                  {$2}
  
fparams:
  | fparam                              {[$1]}
  | fparam fparams                      {$1::$2}
    
restypeopt:
  |                                     {None}
  | COLON typespec                      {Some $2}

name:
  NAME                                  {$1}

letdef:
  LETDEC letspec                        {let pat, e = $2 in Letdef (pat,e)}
  
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
  | NUMTYPE                             {adorn Num}
  | BOOLTYPE                            {adorn Bool}
  | CHARTYPE                            {adorn Char}
  | STRINGTYPE                          {adorn String}
  | BITTYPE                             {adorn Bit}
  | UNITTYPE                            {adorn Unit}
  | GATETYPE                            {adorn Gate}
  | QBITTYPE                            {adorn Qbit}
  | QSTATETYPE                          {adorn Qstate}
  | typevar                             {adorn (Known ($1))}
/*  | INT DOTDOT INT                      {let low = int_of_string $1 in
                                         let high = int_of_string $3 in
                                         if low<=high then adorn (Range (low,high))
                                         else raise (ParseError (get_sourcepos(), "low>high in range type"))
                                        } */
  | LPAR typespec RPAR                  {$2}
  | FORALL typevars DOT typespec        {adorn (Poly ($2,$4))}
  | simple_typespec LISTTYPE            {adorn (List ($1))}
  
simple_typespecs:
  | simple_typespec                     {[$1]}
  | simple_typespec STAR simple_typespecs
                                        {$1::$3}
                                        
typevar:
  TVNAME                                {$1}
    
typevars:
  | typevar                             {[$1]}
  | typevar COMMA typevars              {$1::$3}
  
parsep:
  | PARSEP                              {}
  
process:
  | sumprocess                          {adorn (GSum $1)}
  | parprocess                          {adorn (Par $1)}
  | simpleprocess                       {$1}
  
parprocess:
  | onepar                               {[$1]}
  | onepar parprocess                    {$1::$2}

onepar:
  | PARSEP indentHere indentNext process outdent outdent
                                        {$4}

sumprocess:
  | sumproc                             {[$1]}
  | sumproc sumprocess                  {$1::$2}
  
sumproc:
  | PLUS indentHere indentNext iostep DOT process outdent outdent
                                        {$4,$6}

qstep:
  | expr MEASURE mpat                   {adorn (Measure ($1,None,$3))}
  | expr MEASURE LSQPAR RSQPAR mpat     {adorn (Measure ($1,None,$5))}
  | expr MEASURE LSQPAR expr RSQPAR mpat       
                                        {adorn (Measure ($1,Some $4,$6))}
  | nwexpr THROUGH expr                 {adorn (Ugatestep (Expr.relist $1,$3))}

mpat:
  | UNDERSCORE                          {padorn (PatAny)}
  | LPAR UNDERSCORE RPAR                {padorn (PatAny)}
  | LPAR name RPAR                      {padorn (PatName $2)}
  | LPAR name COLON typespec RPAR       {adorn (pwrap (Some $4) (PatName $2))}

iostep:
  | expr QUERY LPAR bpattern RPAR       {adorn (Read ($1,$4))}
  | expr QUERY UNDERSCORE               {adorn (Read ($1, padorn PatAny))}
  | expr BANG expr                      {adorn (Write ($1,$3))}

simpleprocess:
  | TERMINATE                           {adorn Terminate}
  | procname primary                    {adorn (Call ($1,match $2.inst.enode with 
                                                         | EUnit     -> []
                                                         | ETuple es -> es
                                                         | _         -> [$2]
                                                     )
                                               )
                                        }
  | LPAR NEWDEC paramseq RPAR process   
                                        {adorn (WithNew ($3,$5))}
  | LPAR QBITDEC qspecs RPAR process    
                                        {adorn (WithQbit ($3,$5))}
  | LPAR LETDEC letspec RPAR process    
                                        {adorn (WithLet ($3,$5))}
  | qstep DOT process                   
                                        {adorn (WithQstep ($1,$3))}
  | iostep DOT process                  {adorn (GSum [$1,$3])}
  /* this MATCH rule _must_ have exactly the same indent/outdent pattern as the expression MATCH rule */
  | MATCH 
    indentPrev 
      indentNext expr outdent
      DOT 
      indentNext procmatches outdent
    outdent                             {adorn (PMatch ($4,$8))}
  | LPAR process RPAR                   {$2}
  | IF ubif FI                          {$2}

procmatches:
  | procmatch                           {[$1]}
  | procmatch procmatches               {$1::$2}
  
procmatch:
  | PLUS indentHere 
           indentNext pattern outdent 
           DOT 
           indentNext process outdent 
         outdent    
                                        {$4,$8}
  
ubif: 
  | expr THEN process ELSE process      {adorn (Cond ($1, $3, $5))}
  | expr THEN process ELIF ubif         {adorn (Cond ($1, $3, $5))}
  

qspecs:
  | qspec                               {[$1]}
  | qspec COMMA qspecs                  {$1::$3}

qspec:
  | param                               {let q = $1, None in
                                         if !(Settings.verbose) then Printf.printf "seen qspec %s\n" (string_of_qspec q);
                                         q
                                        }
  | param EQUALS ntexpr                 {let q = $1, Some $3 in
                                         if !(Settings.verbose) then Printf.printf "seen qspec %s\n" (string_of_qspec q);
                                         q
                                        }
  
letspec:
  | bpattern EQUALS indentNext expr outdent
                                        {$1, $4}
  
args:
  |                                     {[]}
  | ntexprs                             {$1}

pattern:
  | conspattern                         {if !(Settings.verbose) then Printf.printf "seen pattern %s\n" (string_of_pattern $1); $1}
  | conspattern COMMA tuplepattern      {let p = padorn (Pattern.delist ($1::$3)) in
                                         if !(Settings.verbose) then Printf.printf "seen pattern %s\n" (string_of_pattern p);
                                         p
                                        }
  
tuplepattern:
  | conspattern                         {[$1]}
  | conspattern COMMA tuplepattern      {$1::$3}
  
conspattern:
  | simplepattern                       {$1}
  | simplepattern CONS conspattern      {padorn (PatCons ($1,$3))}
  
simplepattern:
  | UNDERSCORE                          {padorn PatAny}
  | name                                {padorn (PatName $1)}
  | BIT0                                {padorn (PatBit false)}
  | BIT1                                {padorn (PatBit true)}
  | NUM                                 {padorn (PatInt (int_of_string $1))}
  | TRUE                                {padorn (PatBool (true))}
  | FALSE                               {padorn (PatBool (false))}
  | CHAR                                {padorn (PatChar $1)}
  | STRING                              {padorn (PatString $1)}
  | basisv                              {padorn (PatBasisv $1) }
  | LSQPAR patternlist RSQPAR           {$2}
  | LPAR RPAR                           {padorn PatUnit}
  | LPAR pattern RPAR                   {$2}
  | simplepattern COLON typespec        {adorn (pwrap (Some $3) $1.inst.pnode)}
  
patternlist:
  |                                     {padorn PatNil}
  | pattern                             {padorn (PatCons ($1, padorn PatNil))}
  | pattern SEMICOLON patternlist       {padorn (PatCons ($1,$3))}
  
patterns:
  | pattern                             {[$1]}
  | pattern COMMA patterns              {$1::$3}
  
/* simpler form of pattern for lets, reads, and (for now) function defs. Can't fail to match */
bpattern:
  | simplebpattern                      {$1}                
  | simplebpattern COMMA bpatterns      {padorn (Pattern.delist ($1::$3))}
  
bpatterns:
  | simplebpattern                      {[$1]}                
  | simplebpattern COMMA bpatterns      {$1::$3}
  
simplebpattern:
  | UNDERSCORE                          {padorn PatAny}
  | LPAR RPAR                           {padorn PatUnit}
  | name                                {padorn (PatName $1)}
  | LPAR bpattern RPAR                  {$2}
  | simplebpattern COLON typespec       {adorn (pwrap (Some $3) $1.inst.pnode)}
  
basisv:
  | VZERO                               {BVzero }
  | VONE                                {BVone  }
  | VPLUS                               {BVplus }
  | VMINUS                              {BVminus}

primary:
  | LPAR RPAR                           {eadorn EUnit}
  | name                                {eadorn (EVar $1)}
  | BIT0                                {eadorn (EBit false)}
  | BIT1                                {eadorn (EBit true)}
  | NUM                                 {eadorn (ENum (Number.num_of_string $1))}
  | TRUE                                {eadorn (EBool (true))}
  | FALSE                               {eadorn (EBool (false))}
  | CHAR                                {eadorn (EChar $1)}
  | STRING                              {eadorn (EString $1)}
  | basisv                              {eadorn (EBasisv $1) }
  | LSQPAR exprlist RSQPAR              {$2}
  | LPAR expr RPAR                      {eadorn (Expr.delist (Expr.relist $2))}
  | IF eif FI                           {eadorn($2.inst.enode)}
  /* this MATCH rule has to have exactly the same indent/outdent pattern as the process MATCH rule */
  | MATCH 
    indentPrev 
      indentNext expr outdent
      DOT 
      indentNext ematches outdent
    outdent                             {eadorn (EMatch ($4,$8))}
  
eif:
  | expr THEN expr ELSE expr            {eadorn (ECond ($1,$3,$5))}
  | expr THEN expr ELIF eif             {eadorn (ECond ($1,$3,$5))}
  
ematches:
  | ematch                              {[$1]}
  | ematch ematches                     {$1::$2}
  
ematch:
  | PLUS indentHere indentNext pattern outdent DOT indentNext expr outdent outdent             
                                        {$4,$8}
  
expr:
  | nwexpr                              {$1}
  | expr WHERE indentPrev edecl outdent    
                                        {eadorn (EWhere ($1,$4))}
  
edecl:
  | bpattern restypeopt EQUALS indentNext expr outdent
                                        {adorn (EDPat($1,$2,$5))}
  | funname fparams restypeopt EQUALS indentNext expr outdent   
                                        {let rt = ref $3 in adorn (EDFun($1,$2,rt,$6))}

nwexpr:  
  | ntexpr                              {$1}
  | ntexpr COMMA ntexprs                {eadorn (ETuple ($1::$3))}

ntexprs:
  | ntexpr                              {[$1]}
  | ntexpr COMMA ntexprs                {$1::$3}

ntexpr:  /* a non-tuple expression -- can be a cons */
  | ntlexpr                             {$1}
  | ntlexpr CONS ntexpr                 {eadorn (ECons ($1,$3))}
  
ntlexpr: /* neither tuple nor cons */
  | primary                             {$1} 
  | app                                 {$1}
  | MINUS primary                       {eadorn (EMinus $2)}
  | NOT primary                         {eadorn (ENot $2)}
  | ntexpr APPEND ntexpr                {eadorn (EAppend ($1,$3))}
  | arith                               {let e1,op,e2 = $1 in eadorn (EArith (e1,op,e2))}
  | compare                             {let e1,op,e2 = $1 in eadorn (ECompare (e1,op,e2))}
  | bool                                {let e1,op,e2 = $1 in eadorn (EBoolArith (e1,op,e2))}
  | LAMBDA fparams DOT expr             {eadorn (ELambda ($2,$4))} /* oh dear expr not ntexpr? */

app:
  | primary primary                     {eadorn (EApp ($1,$2))}
  | app primary                         {eadorn (EApp ($1,$2))}
  
arith:
  | ntexpr TENSORP ntexpr               {$1,TensorP,$3}
  | ntexpr STAR ntexpr                  {$1,Times,$3}
  | ntexpr DIV ntexpr                   {$1,Div,$3}
  | ntexpr MOD ntexpr                   {$1,Mod,$3}
  | ntexpr PLUS ntexpr                  {$1,Plus,$3}
  | ntexpr MINUS ntexpr                 {$1,Minus,$3}
  
compare:
  | ntexpr compareop ntexpr %prec EQUALS           
                                        {$1,$2,$3}
  
compareop:
  | LESS                                {Lt}
  | LESSEQUAL                           {Leq}
  | EQUALS                              {Eq}
  | GREATEREQUAL                        {Geq}
  | GREATER                             {Gt}
  | NOTEQUAL                            {Neq}

bool:
  | ntexpr AND ntexpr                   {$1,And,$3}
  | ntexpr OR ntexpr                    {$1,Or,$3}
  
exprlist:
  |                                     {eadorn ENil}
  | expr                                {eadorn (ECons ($1, eadorn ENil))}
  | expr SEMICOLON exprlist             {eadorn (ECons ($1, $3))}

exprs:  /* not the same as exprlist */
  |                                     {[]}
  | expr                                {[$1]}
  | expr SEMICOLON exprs                {$1::$3}
  
names:
  | name                                {[$1]}
  | name COMMA names                    {$1::$3}
  
/* entry point for reading types to save brain when defining contexts */

readtype:
  | typespec EOP                       {$1}
  
/* entry point for reading types to save brain when testing new typechecker */

readexpr:
  | expr EOP                            {$1}

%%
