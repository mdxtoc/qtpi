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

/* this file is still an ocamlyacc file, because menhir doesn't seem to be able to
   handle the pseudo-rules that do the offside parsing. But it still needs an elaborate 
   dance to interface with the Sedlex lexer, and that comes from MenhirLib: see parserutils.ml
 */
 
%{
  open Settings
  open Parserparams
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
  
  let loc() = Parsing.symbol_start_pos(), Parsing.symbol_end_pos()

  let adorn inst = Instance.adorn (loc()) inst
  
  let tadorn inst = Type.tadorn (loc()) inst
    
  let procadorn inst = Process.procadorn (loc()) inst
         
%}

%token <string>       NUM
%token <string>       NAME 
%token <string>       TVNAME 
%token <string>       TPNUM 
%token <Uchar.t list> STRING 
%token <string>       BRA
%token <string>       KET
%token <Uchar.t>      CHAR /* oh dear ... */

%token EOP OFFSIDE /* could it be EOP? No. */
%token FUN PROC WHERE LAMBDA WITH TESTPOINT LEFTREPEAT RIGHTREPEAT
%token LPAR RPAR LBRACE RBRACE LSQPAR RSQPAR PARSEP COLON
%token IF THEN ELSE ELIF FI
%token NUMTYPE BOOLTYPE CHARTYPE STRINGTYPE GATETYPE SXNUMTYPE
%token QBITTYPE QBITSTYPE QSTATETYPE CHANTYPE BITTYPE MATRIXTYPE BRATYPE KETTYPE RIGHTARROW
%token DOT DOTDOT UNDERSCORE
%token RESSHOW RESSHOWQ RESCOMPARE
%token NEWDEC UNTRACED QBITDEC QBITSDEC QBITSJOIN QBITSSPLIT LETDEC MATCH 
%token QUERY BANG MEASURE MEASURES THROUGH THROUGHS 
%token PLUS MINUS DIV MOD POW TENSORPROD TENSORPOWER DAGGER
%token DOWNARROW
%token EQUALS NOTEQUAL LESSEQUAL LESS GREATEREQUAL GREATER
%token APPEND CONS
%token AND OR NOT
%token UNIT TERMINATE
%token COMMA STAR SEMICOLON LEFTARROW
%token TRUE FALSE BIT0 BIT1 PI
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

%right RIGHTARROW
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
  | process WITH indentPrev monitor outdent 
                                        {$1, $4}

monitor:
  | monitorelement                      {[$1]}
  | monitorelement monitor              {$1::$2}

monitorelement:
  | montpnum COLON indentHere process outdent
                                        {$1.inst,($1.pos,$4)}

montpnum:
  | tpnum                               {adorn $1}
  
procparams:
  |                                     {[]}
  | paramseq                            {$1}
  
paramseq:
  | param                               {[$1]}
  | param COMMA paramseq                {$1::$3}
  
param:
  | name COLON typespec                 {adorn (twrap (Some $3) $1)}
  | name                                {tadorn $1}

functiondefs:
  FUN fdefs                             {Functiondefs $2}
  
fdefs:
  | fdef                                {[$1]}
  | fdef fdefs                          {$1::$2}

fdef:
  typedname fparams restypeopt EQUALS indentNext expr outdent    
                                        {$1,$2,ref None,$6}
  
typedname:
  name                                  {tadorn $1}

typednames:
  | typedname                           {[$1]}
  | typedname COMMA typednames          {$1::$3}
  
fparam:
  | name                                {tadorn (PatName $1)}
  | UNDERSCORE                          {tadorn PatAny}
  | LPAR RPAR                           {tadorn PatUnit}
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
  | chan_typespec RIGHTARROW func_typespec    
                                        {adorn (Fun ($1,$3))}
  
chan_typespec:
  | simple_typespec                     {$1}
  | CHANTYPE simple_typespec            {adorn (Channel $2)}
  
simple_typespec:
  | NUMTYPE                             {adorn Num}
  | BOOLTYPE                            {adorn Bool}
  | CHARTYPE                            {adorn Char}
  | STRINGTYPE                          {adorn (List (adorn Char))}
  | BITTYPE                             {adorn Bit}
  | GATETYPE                            {adorn Gate}
  | SXNUMTYPE                           {adorn Sxnum}
  | QBITTYPE                            {adorn Qubit}
  | QBITSTYPE                           {adorn Qubits} 
  | QSTATETYPE                          {adorn Qstate}
  | MATRIXTYPE                          {adorn Matrix}
  | BRATYPE                             {adorn Bra}
  | KETTYPE                             {adorn Ket}
  
  | typevar                             {adorn (Known (uname_of_string $1))}
  
/*  | INT DOTDOT INT                    {let low = int_of_string $1 in
                                         let high = int_of_string $3 in
                                         if low<=high then adorn (Range (low,high))
                                         else raise (ParseError (get_sourcepos(), "low>high in range type"))
                                        } */
  | LPAR RPAR                           {adorn Unit}
  | LPAR typespectuple RPAR             {adorn (Type.delist $2)}
  | FORALL typevars DOT typespec        {adorn (Poly (List.map uname_of_string $2,$4))}
  | LSQPAR typespec RSQPAR              {adorn (List ($2))}
  
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
  | expr measure mpat                   {adorn (Measure ($2,$1,None,$3))}
  | expr measure LSQPAR RSQPAR mpat     {adorn (Measure ($2,$1,None,$5))}
  | expr measure LSQPAR expr RSQPAR mpat       
                                        {adorn (Measure ($2,$1,Some $4,$6))}
  | exprtuple through expr              {adorn (Through ($2,$1,$3,ref false))} /* we don't know it's unique */

measure:
  | MEASURE                             {false}
  | MEASURES                            {true}

through:
  | THROUGH                             {false}
  | THROUGHS                            {true}

mpat:
  | UNDERSCORE                          {tadorn (PatAny)}
  | LPAR UNDERSCORE RPAR                {tadorn (PatAny)}
  | LPAR name RPAR                      {tadorn (PatName $2)}
  | LPAR name COLON typespec RPAR       {adorn (twrap (Some $4) (PatName $2))}

iostep:
  | expr QUERY LPAR bpattern RPAR       {adorn (Read ($1,$4))}
  | expr QUERY UNDERSCORE               {adorn (Read ($1, tadorn PatAny))}
  | expr BANG expr                      {adorn (Write ($1,$3))}
  | expr BANG exprtuple                 {adorn (Write ($1, tadorn (Expr.delist $3)))}

simpleprocess:
  | typedname procargs                  {adorn (GoOnAs ($1,$2))}
  | typedname procargs DOT              {raise (LexposParseError "nothing can follow a process invocation")}
  | LPAR NEWDEC paramseq RPAR process   
                                        {adorn (WithNew ((true,$3),$5))}
  | LPAR NEWDEC UNTRACED paramseq RPAR process   
                                        {adorn (WithNew ((false,$4),$6))}
  | LPAR QBITDEC qspecs RPAR process    
                                        {adorn (WithQubit (false,$3,$5))}
  | LPAR QBITSDEC qspecs RPAR process    
                                        {adorn (WithQubit (true,$3,$5))}
  | LPAR LETDEC letspec RPAR process    
                                        {adorn (WithLet ($3,$5))}
  | LPAR QBITSJOIN typednames RIGHTARROW param RPAR process
                                        {adorn (JoinQs($3,$5,$7))}
  | LPAR QBITSSPLIT typedname RIGHTARROW splitspecs RPAR process
                                        {let specs = $5 in
                                         let blanks = List.filter (function (_,None) -> true | _ -> false) specs in
                                         if List.length blanks>1 then
                                           raise (ParseError (loc(), "more than one unsized collection on right-hand side of →"));
                                         adorn (SplitQs($3,$5,$7))
                                        }
  | qstep dotprocess                   
                                        {adorn (WithQstep ($1,$2))}
  | iostep dotprocess                   {adorn (GSum [$1,$2])}
  | TESTPOINT tpnum process             {adorn (TestPoint (adorn $2,$3))}
  | LSQPAR bpattern LEFTARROW expr COLON process RSQPAR dotprocess /* alternative syntax for Iter ... */
                                        {adorn (Iter ($2,$4,$6,$8))}
  | LEFTREPEAT indentHere bpattern LEFTARROW expr COLON indentNext process outdent outdent dacapoq
             dotprocess
                                        {adorn (Iter ($3,$5,$8,$12))}
  /* this MATCH rule _must_ have exactly the same indent/outdent pattern as the expression MATCH rule 
     (if not, the parsing goes haywire)
   */
  | MATCH 
    indentPrev 
      indentNext expr outdent
      DOT 
      indentNext procmatches outdent
    outdent                             {adorn (PMatch ($4,$8))}
  | LPAR process RPAR                   {$2}
  | IF indentPrev ubif outdent fiq      {$3}
  | DOT process                         {$2} /* optional extra dots ... */
  | TERMINATE                           {warning (loc()) "_0 as empty process is deprecated: use () or nothing at all";
                                         adorn Terminate
                                        }
  | LPAR RPAR                           {adorn Terminate} /* hope this works */
  |                                     {adorn Terminate} /* hope this works */

dotprocess:
  | DOT process                         {$2}
  | TESTPOINT tpnum dotprocess          {adorn (TestPoint (adorn $2,$3))}
  
dacapoq:    /* optional 𝄇 */
  | RIGHTREPEAT                         {}
  |                                     {}
  
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
                                        {adorn (Cond ($2, $6, $11))}
  | indentNext expr outdent 
    THEN indentNext process outdent     /* can go back beyond THEN, but not beyond IF */ 
    ELIF indentPrev ubif outdent        {adorn (Cond ($2, $6, $10))}
  

qspecs:
  | qspec                               {[$1]}
  | qspec COMMA qspecs                  {$1::$3}

qspec:
  | param                               {$1, None}
  | param EQUALS nwexpr                 {$1, Some $3}

splitspecs:
  | splitspec                           {[$1]}
  | splitspec COMMA splitspecs          {$1::$3}

splitspec:
  | param                               {$1, None}
  | param LPAR nwexpr RPAR              {$1, Some $3}
  
letspec:
  | bpattern EQUALS indentNext expr outdent
                                        {$1, $4}
  
pattern:
  | simplepattern                       {$1}
  | simplepattern CONS pattern          {tadorn (PatCons ($1,$3))}
  
simplepattern:
  | UNDERSCORE                          {tadorn PatAny}
  | name                                {tadorn (PatName $1)}
  | BIT0                                {tadorn (PatBit false)}
  | BIT1                                {tadorn (PatBit true)}
  | NUM                                 {tadorn (PatInt (int_of_string $1))}
  | TRUE                                {tadorn (PatBool (true))}
  | FALSE                               {tadorn (PatBool (false))}
  | CHAR                                {tadorn (PatChar $1)}
  | STRING                              {tadorn (PatString $1)}
  | BRA                                 {tadorn (PatBra (bkelements_of_string $1)) }
  | KET                                 {tadorn (PatKet (bkelements_of_string $1)) }
  | LSQPAR patternlist RSQPAR           {$2}
  | LPAR RPAR                           {tadorn PatUnit}
  | LPAR patterns RPAR                  {tadorn (Pattern.delist $2)}
  | simplepattern COLON typespec        {adorn (twrap (Some $3) (tinst $1))}
  
patternlist:
  |                                     {tadorn PatNil}
  | pattern                             {tadorn (PatCons ($1, tadorn PatNil))}
  | pattern SEMICOLON patternlist       {tadorn (PatCons ($1,$3))}
  
patterns:   /* no 'empty' alternative */
  | pattern                             {[$1]}
  | pattern COMMA patterns              {$1::$3}
  
/* simpler form of pattern for lets, reads, and (for now) function defs. Can't fail to match */
bpattern:
  | simplebpattern                      {$1}                
  | simplebpattern COMMA bpatterns      {tadorn (Pattern.delist ($1::$3))}
  
bpatterns:
  | simplebpattern                      {[$1]}                
  | simplebpattern COMMA bpatterns      {$1::$3}
  
simplebpattern:
  | UNDERSCORE                          {tadorn PatAny}
  | LPAR RPAR                           {tadorn PatUnit}
  | name                                {tadorn (PatName $1)}
  | LPAR bpattern RPAR                  {$2}
  | simplebpattern COLON typespec       {adorn (twrap (Some $3) (tinst $1))}

tpnum:
  | NUM                                 {$1}
  | TPNUM                               {$1}
  
primary:
  | LPAR expr COLON typespec RPAR       {adorn (twrap (Some $4) (tinst $2))}
  | LPAR RPAR                           {tadorn EUnit}
  | name                                {tadorn (EVar $1)}
  | RESSHOW                             {tadorn (ERes (ResShow false))}
  | RESSHOWQ                            {tadorn (ERes (ResShow true))}
  | RESCOMPARE                          {tadorn (ERes ResCompare)}
  | BIT0                                {tadorn (EBit false)}
  | BIT1                                {tadorn (EBit true)}
  | PI                                  {tadorn EPi}
  | NUM                                 {tadorn (ENum (Number.num_of_string $1))}
  | TRUE                                {tadorn (EBool (true))}
  | FALSE                               {tadorn (EBool (false))}
  | CHAR                                {tadorn (EChar $1)}
  | STRING                              {tadorn (EString $1)}
  | BRA                                 {tadorn (EBra (bkelements_of_string $1)) }
  | KET                                 {tadorn (EKet (bkelements_of_string $1)) }
  | LSQPAR exprlist RSQPAR              {$2}
  | LPAR exprtuple RPAR                 {tadorn (Expr.delist $2)} /* tuples must be bracketed, a la Miranda */
  | IF indentPrev eif outdent fiq       {tadorn(tinst $3)}
  /* this MATCH rule has to have exactly the same indent/outdent pattern as the process MATCH rule */
  | MATCH 
    indentPrev 
      indentNext expr outdent
      DOT 
      indentNext ematches outdent
    outdent                             {tadorn (EMatch ($4,$8))}
  
eif:
  | indentNext expr outdent 
    THEN indentNext expr outdent        /* can go back beyond THEN, but not beyond IF */ 
    ELSE indentNext expr outdent        /* ditto */
                                        {tadorn (ECond ($2, $6, $10))}
  | indentNext expr outdent 
    THEN indentNext expr outdent        /* can go back beyond THEN, but not beyond IF */ 
    ELIF indentPrev eif outdent         {tadorn (ECond ($2, $6, $10))}
  
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
                                        {tadorn (EWhere ($1,$4))}
  
edecl:
  | bpattern restypeopt EQUALS indentNext expr outdent
                                        {adorn (EDPat($1,$2,$5))}
  | typedname fparams restypeopt EQUALS indentNext expr outdent   
                                        {let rt = ref $3 in adorn (EDFun($1,$2,rt,$6))}

nwexpr:  /* non-while expr: can be a cons */
  | nwlexpr                             {$1}
  | nwlexpr CONS nwexpr                 {tadorn (ECons ($1,$3))}
  
nwlexpr: /* neither while nor cons */
  | primary                             {$1} 
  | app                                 {$1}
  | MINUS primary                       {tadorn (EMinus $2)}
  | NOT primary                         {tadorn (ENot $2)}
  | nwexpr APPEND nwexpr                {tadorn (EAppend ($1,$3))}
  | primary DAGGER                      {tadorn (EDagger $1)}
  | primary DOWNARROW nwexpr            {tadorn (ESub ($1,$3))}
  | arith                               {let e1,op,e2 = $1 in tadorn (EArith (e1,op,e2))}
  | compare                             {let e1,op,e2 = $1 in tadorn (ECompare (e1,op,e2))}
  | bool                                {let e1,op,e2 = $1 in tadorn (EBoolArith (e1,op,e2))}
  | LAMBDA fparams DOT expr             {tadorn (ELambda ($2,$4))} /* oh dear expr not nwexpr? */

app:
  | primary primary                     {tadorn (EJux ($1,$2))}
  | app primary                         {tadorn (EJux ($1,$2))}
  
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
  |                                     {tadorn ENil}
  | expr                                {tadorn (ECons ($1, tadorn ENil))}
  | expr SEMICOLON exprlist             {tadorn (ECons ($1, $3))}

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
