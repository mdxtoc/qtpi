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
 
exception Can'tHappen of string (* for anybody to use *)
exception Error of string       (* ditto *)
exception LibraryError of string
exception ParseError of Sourcepos.sourcepos * string (* because I can't put it in Parser, and I have to put it somewhere *)
exception LexposParseError of string                 (* ditto *)

let temp_setting vref v f =
  let oldv = !vref in
  vref := v;
  try
    let result = f () in
    vref := oldv;
    result
  with exn -> vref:=oldv; raise exn
  
let chanbuf_limit = ref 0           (* buffer limit for channels: -1 for infinite, 0 for synchronisation *)

let checkrandombias = ref false

let complexcombine = ref true

let factorbraket = ref true

type fancynum = RawNum | FractionalNum 

let fancynum = ref FractionalNum

let fancyvec = ref true

let func_matrices = ref true

(* let detectdisposes = ref true *)

let gatingsimplifies = ref false

let interpret = ref true

let matchcheck = ref true

let measuredestroys = ref true

let memoise = ref true

(* let pstep = ref false *)

let showqsimplifies = ref true

let resourcecheck = ref true

let rootcombine = ref true

let runbraket = ref true

let show_final = ref false

let showabvalues = ref false

let showdensematrices = ref false

let showstepcount = ref false

let showsymbolicgate = ref true

let showunknownparts = ref false

let splitplurals = ref true

let symbq = ref true

let symbolic_ht = ref true

let usetestpoints = ref true

let traceevents = ref false
let traceId = ref false
let traceIO = ref false

let trydiag = ref true (* why not? I think it's only Grover that cares *)

let typereport = ref false

let verbose             = ref false
let verbose_compile     = ref false
let verbose_interpret   = ref false
let verbose_matchcheck  = ref false
let verbose_measure     = ref false
let verbose_memo        = ref false
let verbose_offside     = ref false 
let verbose_qsim        = ref false
let verbose_qcalc       = ref false
let verbose_queues      = ref false
let verbose_resource    = ref false
let verbose_simplify    = ref false
let verbose_trace       = ref false
let verbose_typecheck   = ref false

let verboseopts = [("all"              , verbose                  );
                   ("compile"          , verbose_compile          );
                   ("interpret"        , verbose_interpret        );
                   ("matchcheck"       , verbose_matchcheck       );
                   ("measure"          , verbose_measure          );
                   ("memo"             , verbose_memo             );
                   ("offside"          , verbose_offside          );
                   ("qcalc"            , verbose_qcalc            );
                   ("qsim"             , verbose_qsim             );
                   ("queues"           , verbose_queues           );
                   ("resource"         , verbose_resource         );
                   ("simplify"         , verbose_simplify         );
                   ("trace"            , verbose_trace            );
                   ("typecheck"        , verbose_typecheck        );
                  ] 

let setverbose s = (List.assoc s verboseopts) := true

let fancynumopts = [("raw"       , RawNum);
                    ("fractional", FractionalNum)
                   ]

let setfancynum s = fancynum := List.assoc s fancynumopts

let decode_fancynum () = let ss, ns = List.split fancynumopts in
                         let revopts = List.combine ns ss in
                         List.assoc !fancynum revopts
                         
let temp_setting vref v f =
  let oldv = !vref in
  vref := v;
  try
    let result = f () in
    vref := oldv;
    result
  with exn -> vref:=oldv; raise exn
  
let push_verbose v f = 
  temp_setting verbose (!verbose||v) f
  