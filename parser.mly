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

/* this file was once an ocamlyacc file, but menhir seems to be a better parser-generator.
   The downside of menhir is that it needs the $loc parameter: can't be done, as it once
   was, in the OCaml header. And it needs an elaborate dance to interface with the 
   Sedlex lexer: see parserutils.ml
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
  open Braket
  open Pattern
  open Sourcepos
  open Instance
  
  exception ParserCrash of string
  
  let adorn = Instance.adorn
  
  let tadorn = Type.tadorn
    
  let procadorn = Process.procadorn
         
%}

%token <string> NUM
%token <string> NAME 
%token <string> TVNAME 
%token <string> TPNUM 
%token <string> STRING 
%token <string> BRA
%token <string> KET
%token <Uchar.t> CHAR /* oh dear ... */

%token EOP OFFSIDE /* could it be EOP? No. */
%token FUN PROC WHERE LAMBDA WITH TESTPOINT PROCITER
%token LPAR RPAR LBRACE RBRACE LSQPAR RSQPAR PARSEP COLON
%token IF THEN ELSE ELIF FI
%token NUMTYPE BOOLTYPE CHARTYPE STRINGTYPE GATETYPE QBITTYPE QSTATETYPE CHANTYPE BITTYPE MATRIXTYPE BRATYPE KETTYPE TYPEARROW
%token DOT DOTDOT UNDERSCORE
%token NEWDEC UNTRACED QBITDEC LETDEC MATCH 
%token QUERY BANG MEASURE THROUGH 
%token PLUS MINUS DIV MOD POW TENSORPROD TENSORPOWER
%token EQUALS NOTEQUAL LESSEQUAL LESS GREATEREQUAL GREATER
%token APPEND CONS
%token AND OR NOT
%token UNIT TERMINATE
%token COMMA STAR SEMICOLON LEFTARROW
%token TRUE FALSE BIT0 BIT1
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
%left mult_op STAR DIV MOD POW
%left TENSORPROD TENSORPOWER
%left APPEND

%right TYPEARROW
/* %nonassoc STAR */

%start program             /* Entry point */
%start readtype
%start readexpr
%start readpdef

%type  <Def.def list> program
%type  <Type._type> readtype
%type  <Expr.expr> readexpr
%type  <Def.pdef> readpdef

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
  | processdefs                         {$1}
  | functiondefs                        {$1}
  | letdef                              {$1}
  
processdefs:
  PROC pdefs                            {Processdefs $2}

pdefs:
  | pdef                                {[$1]}
  | pdef pdefs                          {$1::$2}
  
pdef:
  typedname LPAR procparams RPAR EQUALS indentNext processbody outdent
                                        {let proc, monbody = $7 in
                                         ($1,$3,proc,monbody)
                                        }

processbody:
  | process                             {$1, []}
  | process WITH monitor                {$1, $3}

monitor:
  | monitorelement                      {[$1]}
  | monitorelement monitor              {$1::$2}

monitorelement:
  | montpnum COLON process              {$1.inst,($1.pos,$3)}

montpnum:
  | tpnum                               {adorn $loc $1}
  
procparams:
  |                                     {[]}
  | paramseq                            {$1}
  
paramseq:
  | param                               {[$1]}
  | param COMMA paramseq                {$1::$3}
  
param:
  | name COLON typespec                 {adorn $loc (twrap (Some $3) $1)}
  | name                                {tadorn $loc $1}

functiondefs:
  FUN fdefs                             {Functiondefs $2}
  
fdefs:
  | fdef                                {[$1]}
  | fdef fdefs                          {$1::$2}

fdef:
  typedname fparams restypeopt EQUALS indentNext expr outdent    
                                        {$1,$2,ref None,$6}
  
typedname:
  name                                  {tadorn $loc $1}
  
fparam:
  | name                                {tadorn $loc (PatName $1)}
  | UNDERSCORE                          {tadorn $loc PatAny}
  | LPAR RPAR                           {tadorn $loc PatUnit}
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
  | typespec PROCESS                    {adorn $loc (Process (Type.relist $1))}

func_typespec:
  | chan_typespec                       {$1}
  | chan_typespec TYPEARROW func_typespec    
                                        {adorn $loc (Fun ($1,$3))}
  
chan_typespec:
  | simple_typespec                     {$1}
  | CHANTYPE simple_typespec            {adorn $loc (Channel $2)}
  
simple_typespec:
  | NUMTYPE                             {adorn $loc Num}
  | BOOLTYPE                            {adorn $loc Bool}
  | CHARTYPE                            {adorn $loc Char}
  | STRINGTYPE                          {adorn $loc String}
  | BITTYPE                             {adorn $loc Bit}
  | GATETYPE                            {adorn $loc Gate}
  | QBITTYPE                            {adorn $loc Qbit}
  | QSTATETYPE                          {adorn $loc Qstate}
  | MATRIXTYPE                          {adorn $loc Matrix}
  | BRATYPE                             {adorn $loc Bra}
  | KETTYPE                             {adorn $loc Ket}
  
  | typevar                             {adorn $loc (Known ($1))}
  
/*  | INT DOTDOT INT                      {let low = int_of_string $1 in
                                         let high = int_of_string $3 in
                                         if low<=high then adorn $loc (Range (low,high))
                                         else raise (ParseError (get_sourcepos(), "low>high in range type"))
                                        } */
  | LPAR RPAR                           {adorn $loc Unit}
  | LPAR typespectuple RPAR             {adorn $loc (Type.delist $2)}
  | FORALL typevars DOT typespec        {adorn $loc (Poly ($2,$4))}
  | LSQPAR typespec RSQPAR              {adorn $loc (List ($2))}
  
simple_typespecs:
  | simple_typespec                     {[$1]}
  | simple_typespec STAR simple_typespecs
                                        {$1::$3}
typespectuple:
  | typespec                            {[$1]}
  | typespec COMMA typespectuple        {$1::$3} 
  
typevar:
  TVNAME                                {$1}
    
typevars:
  | typevar                             {[$1]}
  | typevar COMMA typevars              {$1::$3}
  
parsep:
  | PARSEP                              {}
  
process:
  | sumprocess                          {adorn $loc (GSum $1)}
  | parprocess                          {adorn $loc (Par $1)}
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
  | expr MEASURE mpat                   {adorn $loc (Measure ($1,None,$3))}
  | expr MEASURE LSQPAR RSQPAR mpat     {adorn $loc (Measure ($1,None,$5))}
  | expr MEASURE LSQPAR expr RSQPAR mpat       
                                        {adorn $loc (Measure ($1,Some $4,$6))}
  | exprtuple THROUGH expr              {adorn $loc (Ugatestep ($1,$3))}

mpat:
  | UNDERSCORE                          {tadorn $loc (PatAny)}
  | LPAR UNDERSCORE RPAR                {tadorn $loc (PatAny)}
  | LPAR name RPAR                      {tadorn $loc (PatName $2)}
  | LPAR name COLON typespec RPAR       {adorn $loc (twrap (Some $4) (PatName $2))}

iostep:
  | expr QUERY LPAR bpattern RPAR       {adorn $loc (Read ($1,$4))}
  | expr QUERY UNDERSCORE               {adorn $loc (Read ($1, tadorn $loc PatAny))}
  | expr BANG expr                      {adorn $loc (Write ($1,$3))}
  | expr BANG exprtuple                 {adorn $loc (Write ($1, tadorn $loc (Expr.delist $3)))}

simpleprocess:
  | TERMINATE                           {adorn $loc Terminate}
  | typedname procargs                  {adorn $loc (GoOnAs ($1,$2))}
  | LPAR NEWDEC paramseq RPAR process   
                                        {adorn $loc (WithNew ((true,$3),$5))}
  | LPAR NEWDEC UNTRACED paramseq RPAR process   
                                        {adorn $loc (WithNew ((false,$4),$6))}
  | LPAR QBITDEC qspecs RPAR process    
                                        {adorn $loc (WithQbit ($3,$5))}
  | LPAR LETDEC letspec RPAR process    
                                        {adorn $loc (WithLet ($3,$5))}
  | qstep DOT process                   
                                        {adorn $loc (WithQstep ($1,$3))}
  | iostep DOT process                  {adorn $loc (GSum [$1,$3])}
  | TESTPOINT tpnum process             {adorn $loc (TestPoint (adorn $loc $2,$3))}
  | PROCITER LPAR bpattern RPAR LPAR process RPAR expr DOT process
                                        {adorn $loc (Iter ($3,$8,$6,$10))}
  | LSQPAR bpattern LEFTARROW expr COLON process RSQPAR DOT process /* alternative syntax for Iter ... */
                                        {adorn $loc (Iter ($2,$4,$6,$9))}
  /* this MATCH rule _must_ have exactly the same indent/outdent pattern as the expression MATCH rule 
     (if not, the parsing goes haywire)
   */
  | MATCH 
    indentPrev 
      indentNext expr outdent
      DOT 
      indentNext procmatches outdent
    outdent                             {adorn $loc (PMatch ($4,$8))}
  | LPAR process RPAR                   {$2}
  | IF indentPrev ubif outdent fiq      {$3}
  | DOT process                         {$2} /* I hope this works ... */

procargs:
  | LPAR RPAR                           {[]}
  | LPAR exprtuple RPAR                 {$2}
  
  
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
  | indentNext expr outdent 
    THEN indentNext process outdent     /* can go back beyond THEN, but not beyond IF */ 
    ELSE indentPrev indentNext process outdent outdent     
                                        {adorn $loc (Cond ($2, $6, $11))}
  | indentNext expr outdent 
    THEN indentNext process outdent     /* can go back beyond THEN, but not beyond IF */ 
    ELIF indentPrev ubif outdent        {adorn $loc (Cond ($2, $6, $10))}
  

qspecs:
  | qspec                               {[$1]}
  | qspec COMMA qspecs                  {$1::$3}

qspec:
  | param                               {let q = $1, None in
                                         if !(Settings.verbose) then Printf.printf "seen qspec %s\n" (string_of_qspec q);
                                         q
                                        }
  | param EQUALS nwexpr                 {let q = $1, Some $3 in
                                         if !(Settings.verbose) then Printf.printf "seen qspec %s\n" (string_of_qspec q);
                                         q
                                        }
  
letspec:
  | bpattern EQUALS indentNext expr outdent
                                        {$1, $4}
  
pattern:
  | simplepattern                       {$1}
  | simplepattern CONS pattern          {tadorn $loc (PatCons ($1,$3))}
  
simplepattern:
  | UNDERSCORE                          {tadorn $loc PatAny}
  | name                                {tadorn $loc (PatName $1)}
  | BIT0                                {tadorn $loc (PatBit false)}
  | BIT1                                {tadorn $loc (PatBit true)}
  | NUM                                 {tadorn $loc (PatInt (int_of_string $1))}
  | TRUE                                {tadorn $loc (PatBool (true))}
  | FALSE                               {tadorn $loc (PatBool (false))}
  | CHAR                                {tadorn $loc (PatChar $1)}
  | STRING                              {tadorn $loc (PatString $1)}
  | BRA                                 {tadorn $loc (PatBra (bkelements_of_string $1)) }
  | KET                                 {tadorn $loc (PatKet (bkelements_of_string $1)) }
  | LSQPAR patternlist RSQPAR           {$2}
  | LPAR RPAR                           {tadorn $loc PatUnit}
  | LPAR patterns RPAR                  {tadorn $loc (Pattern.delist $2)}
  | simplepattern COLON typespec        {adorn $loc (twrap (Some $3) (tinst $1))}
  
patternlist:
  |                                     {tadorn $loc PatNil}
  | pattern                             {tadorn $loc (PatCons ($1, tadorn $loc PatNil))}
  | pattern SEMICOLON patternlist       {tadorn $loc (PatCons ($1,$3))}
  
patterns:   /* no 'empty' alternative */
  | pattern                             {[$1]}
  | pattern COMMA patterns              {$1::$3}
  
/* simpler form of pattern for lets, reads, and (for now) function defs. Can't fail to match */
bpattern:
  | simplebpattern                      {$1}                
  | simplebpattern COMMA bpatterns      {tadorn $loc (Pattern.delist ($1::$3))}
  
bpatterns:
  | simplebpattern                      {[$1]}                
  | simplebpattern COMMA bpatterns      {$1::$3}
  
simplebpattern:
  | UNDERSCORE                          {tadorn $loc PatAny}
  | LPAR RPAR                           {tadorn $loc PatUnit}
  | name                                {tadorn $loc (PatName $1)}
  | LPAR bpattern RPAR                  {$2}
  | simplebpattern COLON typespec       {adorn $loc (twrap (Some $3) (tinst $1))}

tpnum:
  | NUM                                 {$1}
  | TPNUM                               {$1}
  
primary:
  | LPAR RPAR                           {tadorn $loc EUnit}
  | name                                {tadorn $loc (EVar $1)}
  | BIT0                                {tadorn $loc (EBit false)}
  | BIT1                                {tadorn $loc (EBit true)}
  | NUM                                 {tadorn $loc (ENum (Number.num_of_string $1))}
  | TRUE                                {tadorn $loc (EBool (true))}
  | FALSE                               {tadorn $loc (EBool (false))}
  | CHAR                                {tadorn $loc (EChar $1)}
  | STRING                              {tadorn $loc (EString $1)}
  | BRA                                 {tadorn $loc (EBra (bkelements_of_string $1)) }
  | KET                                 {tadorn $loc (EKet (bkelements_of_string $1)) }
  | LSQPAR exprlist RSQPAR              {$2}
  | LPAR exprtuple RPAR                 {tadorn $loc (Expr.delist $2)} /* tuples must be bracketed, a la Miranda */
  | IF indentPrev eif outdent fiq       {tadorn $loc(tinst $3)}
  /* this MATCH rule has to have exactly the same indent/outdent pattern as the process MATCH rule */
  | MATCH 
    indentPrev 
      indentNext expr outdent
      DOT 
      indentNext ematches outdent
    outdent                             {tadorn $loc (EMatch ($4,$8))}
  
eif:
  | indentNext expr outdent 
    THEN indentNext expr outdent        /* can go back beyond THEN, but not beyond IF */ 
    ELSE indentPrev indentNext expr outdent outdent
                                        {tadorn $loc (ECond ($2, $6, $11))}
  | indentNext expr outdent 
    THEN indentNext expr outdent        /* can go back beyond THEN, but not beyond IF */ 
    ELIF indentPrev eif outdent         {tadorn $loc (ECond ($2, $6, $10))}
  
fiq:    /* optional FI */
  | FI                                  {}              
  |                                     {}
  
ematches:
  | ematch                              {[$1]}
  | ematch ematches                     {$1::$2}
  
ematch:
  | PLUS indentHere indentNext pattern outdent DOT indentNext expr outdent outdent             
                                        {$4,$8}
  
expr:
  | nwexpr                              {$1}
  | expr WHERE indentPrev edecl outdent    
                                        {tadorn $loc (EWhere ($1,$4))}
  
edecl:
  | bpattern restypeopt EQUALS indentNext expr outdent
                                        {adorn $loc (EDPat($1,$2,$5))}
  | typedname fparams restypeopt EQUALS indentNext expr outdent   
                                        {let rt = ref $3 in adorn $loc (EDFun($1,$2,rt,$6))}

nwexpr:  /* non-while expr: can be a cons */
  | nwlexpr                             {$1}
  | nwlexpr CONS nwexpr                 {tadorn $loc (ECons ($1,$3))}
  
nwlexpr: /* neither while nor cons */
  | primary                             {$1} 
  | app                                 {$1}
  | MINUS primary                       {tadorn $loc (EMinus $2)}
  | NOT primary                         {tadorn $loc (ENot $2)}
  | nwexpr APPEND nwexpr                {tadorn $loc (EAppend ($1,$3))}
  | arith                               {let e1,op,e2 = $1 in tadorn $loc (EArith (e1,op,e2))}
  | compare                             {let e1,op,e2 = $1 in tadorn $loc (ECompare (e1,op,e2))}
  | bool                                {let e1,op,e2 = $1 in tadorn $loc (EBoolArith (e1,op,e2))}
  | LAMBDA fparams DOT expr             {tadorn $loc (ELambda ($2,$4))} /* oh dear expr not nwexpr? */

app:
  | primary primary                     {tadorn $loc (EApp ($1,$2))}
  | app primary                         {tadorn $loc (EApp ($1,$2))}
  
arith:
  | nwexpr TENSORPROD nwexpr            {$1,TensorProd,$3}
  | nwexpr POW nwexpr                   {$1,Power,$3}
  | nwexpr TENSORPOWER nwexpr           {$1,TensorPower,$3}
  | nwexpr STAR nwexpr                  {$1,Times,$3}
  | nwexpr DIV nwexpr                   {$1,Div,$3}
  | nwexpr MOD nwexpr                   {$1,Mod,$3}
  | nwexpr PLUS nwexpr                  {$1,Plus,$3}
  | nwexpr MINUS nwexpr                 {$1,Minus,$3}
  
compare:
  | nwexpr compareop nwexpr %prec EQUALS           
                                        {$1,$2,$3}
  
compareop:
  | LESS                                {Lt}
  | LESSEQUAL                           {Leq}
  | EQUALS                              {Eq}
  | GREATEREQUAL                        {Geq}
  | GREATER                             {Gt}
  | NOTEQUAL                            {Neq}

bool:
  | nwexpr AND nwexpr                   {$1,And,$3}
  | nwexpr OR nwexpr                    {$1,Or,$3}
  
exprlist:
  |                                     {tadorn $loc ENil}
  | expr                                {tadorn $loc (ECons ($1, tadorn $loc ENil))}
  | expr SEMICOLON exprlist             {tadorn $loc (ECons ($1, $3))}

exprtuple:                              /* no 'empty' alternative */
  | expr                                {[$1]}
  | expr COMMA exprtuple                {$1::$3}
    
names:
  | name                                {[$1]}
  | name COMMA names                    {$1::$3}
  
/* entry point for reading types to save brain when defining contexts */

readtype:
  | typespec EOP                       {$1}
  
/* entry point for reading types to save brain when testing new typechecker */

readexpr:
  | expr EOP                            {$1}

/* entry point for reading pdefs to save brain when defining special processes like Iter and Par */

readpdef:
  | pdef EOP                            {$1}
  
%%
