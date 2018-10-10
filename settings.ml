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
 
exception Can'tHappen of string	(* for anybody to use *)

let temp_setting vref v f =
  let oldv = !vref in
  vref := v;
  try
    let result = f () in
    vref := oldv;
    result
  with exn -> vref:=oldv; raise exn
  
let chanbuf_limit = ref 0			(* buffer limit for channels: -1 for infinite, 0 for synchronisation *)

let verbose = ref false
let verbose_interpret = ref false
let verbose_matchcheck = ref false
let verbose_qsim = ref false
let verbose_qcalc = ref false
let verbose_queues = ref false
let verbose_resource = ref false
let verbose_simplify = ref false
let verbose_typecheck = ref false

let symbq = ref true

let fancyvec = ref true

let interpret = ref true

let matchcheck = ref true

let show_final = ref false

let typereport = ref false

let verboseopts = [("all"              , verbose                  );
                   ("interpret"        , verbose_interpret        );
                   ("matchcheck" 	   , verbose_matchcheck		  );
                   ("qcalc"            , verbose_qcalc            );
                   ("qsim"             , verbose_qsim             );
                   ("queues"           , verbose_queues           );
                   ("resource"         , verbose_resource         );
                   ("simplify"         , verbose_simplify         );
                   ("typecheck"        , verbose_typecheck        );
                  ] 

let setverbose s = (List.assoc s verboseopts) := true

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
  