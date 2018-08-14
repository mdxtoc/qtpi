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
    !Settings.filename, Parsing.symbol_start_pos(), Parsing.symbol_end_pos()
  
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

%token <string> INT
%token <string> NAME 
%token <string> STRING 
%token <char> CHAR 

%token EOP 
%token LETR
%token LPAR RPAR LBRACE RBRACE LSQPAR RSQPAR PARSEP SUMSEP MATCHSEP COLON EQUALS
%token IF THEN ELSE ELIF FI
%token INTTYPE BOOLTYPE CHARTYPE STRINGTYPE UNITTYPE QBITTYPE CHANTYPE BITTYPE LISTTYPE TYPEARROW PRIME
%token DOT DOTDOT UNDERSCORE
%token HADAMARD PHI CNOT I X Y Z NEWDEC QBITDEC LETDEC MATCH HCTAM
%token QUERY BANG MEASURE THROUGH 
%token PLUSPLUS PLUS MINUS DIV
%token EQUALS NOTEQUAL LESSEQUAL LESS GREATEREQUAL GREATER
%token APPEND CONS
%token AND OR NOT
%token UNIT TERMINATE
%token COMMA STAR SEMICOLON
%token TRUE FALSE BIT0 BIT1
%token VZERO VONE VPLUS VMINUS
%token FORALL PROCESS

/* remember %left %right %nonassoc and increasing priority */
%right CONS
%left AND OR
%right NOT
%nonassoc EQUALS NOTEQUAL LESSEQUAL LESS GREATEREQUAL GREATER
%left PLUS MINUS PLUSPLUS
%left mult_op DIV
%left APPEND

%right TYPEARROW
%nonassoc STAR

%start program             /* Entry point */
%start readtype
%start readexpr

%type  <Def.def list> program
%type  <Type._type> readtype
%type  <Expr.expr> readexpr

%%
program: defs EOP                       {$1}
                                        
defs:
  | def                                 {[$1]}
  | def defs                            {$1::$2}

def:
  | processdef                          {$1}
  | functiondef                         {$1}
  
processdef:
  procname LPAR procparams RPAR EQUALS process  
                                        {Processdef($1,$3,$6)}

functiondef:
  LETR funname fparams EQUALS expr DOT  {Functiondef($2,$3,$5)} /* oh dear, oh dear. DOT! */
  
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

funname:
  name                                  {adorn $1}
  
fparam:
  | name                                {padorn (PatName $1)}
  | UNDERSCORE                          {padorn PatAny}
  | LPAR bpattern RPAR                  {$2}
  
fparams:
  | fparam                              {[$1]}
  | fparam fparams                      {$1::$2}
    
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
  
parsep:
  | PARSEP                              {}
  
sumsep:
  | SUMSEP                              {}
  
matchsep:
  | SUMSEP                              {}
  
process:
  | sumprocess                          {$1}
  | sumprocess parsep processpar        {adorn (Par ($1::$3))}
  
processpar:
  | sumprocess                          {[$1]}
  | sumprocess parsep processpar        {$1::$3}

sumprocess:
  | ioproc                              {adorn (GSum [$1])}
  | ioproc sumsep processsum            {adorn (GSum ($1::$3))}
  | simpleprocess                       {$1}

processsum:
  | ioproc                              {[$1]}
  | ioproc sumsep processsum            {$1::$3}

ioproc:
  | iostep DOT simpleprocess            {$1,$3}
  
iostep:
  | expr QUERY LPAR bpattern RPAR       {adorn (Read ($1,$4))}
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
  | LPAR NEWDEC paramseq RPAR simpleprocess   
                                        {adorn (WithNew ($3,$5))}
  | LPAR QBITDEC qspecs RPAR simpleprocess    
                                        {adorn (WithQbit ($3,$5))}
  | LPAR LETDEC letspec RPAR simpleprocess    
                                        {adorn (WithLet ($3,$5))}
  | qstep DOT simpleprocess                   
                                        {adorn (WithQstep ($1,$3))}
  | iostep DOT simpleprocess            {adorn (GSum [$1,$3])}
  | LBRACE expr RBRACE DOT simpleprocess      
                                        {adorn (WithExpr ($2,$5))}
  | MATCH expr DOT procmatches HCTAM    {adorn (PMatch ($2,$4))}
  | LPAR process RPAR                   {$2}
  | IF ubif FI                          {$2}

procmatches:
  | procmatch                           {[$1]}
  | procmatch matchsep procmatches      {$1::$3}
  
procmatch:
  | pattern DOT simpleprocess           {$1,$3}
  
ubif: 
  | expr THEN process ELSE process      {adorn (Cond ($1, $3, $5))}
  | expr THEN process ELIF ubif         {adorn (Cond ($1, $3, $5))}
  

qspecs:
  | qspec                               {[$1]}
  | qspec COMMA qspecs                  {$1::$3}

qspec:
  | param                               {$1, None}
  | param EQUALS ntexpr                 {$1, Some $3}
  
letspec:
  | bpattern EQUALS expr                {$1, $3}
  
qstep:
  | expr MEASURE LPAR param RPAR        {adorn (Measure ($1,None,$4))}
  | expr MEASURE LSQPAR expr RSQPAR LPAR param RPAR       
                                        {adorn (Measure ($1,Some $4,$7))}
  | ntexprs THROUGH expr                {adorn (Ugatestep ($1,$3))}

args:
  |                                     {[]}
  | ntexprs                             {$1}

pattern:
  | conspattern                         {$1}
  | conspattern COMMA tuplepattern      {padorn (Pattern.delist ($1::$3))}
  
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
  | INT                                 {padorn (PatInt (int_of_string $1))}
  | TRUE                                {padorn (PatBool (true))}
  | FALSE                               {padorn (PatBool (false))}
  | CHAR                                {padorn (PatChar $1)}
  | STRING                              {padorn (PatString $1)}
  | basisv                              {padorn (PatBasisv $1) }
  | HADAMARD                            {padorn (PatGate (adorn PatH))}
  | CNOT                                {padorn (PatGate (adorn PatCnot))}
  | I                                   {padorn (PatGate (adorn PatI))}
  | X                                   {padorn (PatGate (adorn PatX))}
  | Y                                   {padorn (PatGate (adorn PatY))}
  | Z                                   {padorn (PatGate (adorn PatZ))}
  | PHI LPAR pattern RPAR               {padorn (PatGate (adorn (PatPhi ($3))))}
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
  
/* simpler form of pattern for lets, reads. Can't fail to match */
bpattern:
  | simplebpattern                      {$1}                
  | simplebpattern COMMA bpatterns      {padorn (Pattern.delist ($1::$3))}
  
bpatterns:
  | simplebpattern                      {[$1]}                
  | simplebpattern COMMA bpatterns      {$1::$3}
  
simplebpattern:
  | UNDERSCORE                          {padorn PatAny}
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
  | INT                                 {eadorn (EInt (int_of_string $1))}
  | TRUE                                {eadorn (EBool (true))}
  | FALSE                               {eadorn (EBool (false))}
  | CHAR                                {eadorn (EChar $1)}
  | STRING                              {eadorn (EString $1)}
  | basisv                              {eadorn (EBasisv $1) }
  | ugate                               {eadorn (EGate $1)}
  | LSQPAR exprlist RSQPAR              {$2}
  | LPAR ntexprs RPAR                   {eadorn (Expr.delist $2)}
  | IF eif FI                           {eadorn($2.inst.enode)}
  | MATCH expr DOT ematches HCTAM       {eadorn (EMatch ($2,$4))}
  
eif:
  | expr THEN expr ELSE expr            {eadorn (ECond ($1,$3,$5))}
  | expr THEN expr ELIF eif             {eadorn (ECond ($1,$3,$5))}
  
ematches:
  | ematch                              {[$1]}
  | ematch matchsep ematches            {$1::$3}
  
ematch:
  | pattern DOT expr                    {$1,$3}
  
expr:
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
  | ntexpr PLUSPLUS ntexpr              {eadorn (EBitCombine ($1,$3))}
  | ntexpr APPEND ntexpr                {eadorn (EAppend ($1,$3))}
  | arith                               {let e1,op,e2 = $1 in eadorn (EArith (e1,op,e2))}
  | compare                             {let e1,op,e2 = $1 in eadorn (ECompare (e1,op,e2))}
  | bool                                {let e1,op,e2 = $1 in eadorn (EBoolArith (e1,op,e2))}

app:
  | primary primary                     {eadorn (EApp ($1,$2))}
  | app primary                         {eadorn (EApp ($1,$2))}
  
arith:
  | ntexpr STAR ntexpr %prec mult_op    {$1,Times,$3}
  | ntexpr DIV ntexpr                   {$1,Div,$3}
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
  
ugate: 
  | HADAMARD                            {adorn GH}
  | CNOT                                {adorn GCnot}
  | I                                   {adorn GI}
  | X                                   {adorn GX}
  | Y                                   {adorn GY}
  | Z                                   {adorn GZ}
  | PHI LPAR expr RPAR                  {adorn (GPhi ($3))}

exprlist:
  |                                     {eadorn ENil}
  | expr                                {eadorn (ECons ($1, eadorn ENil))}
  | expr SEMICOLON exprlist             {eadorn (ECons ($1, $3))}

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
