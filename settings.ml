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
    along with Qtpi; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*)
 
let temp_setting vref v f =
  let oldv = !vref in
  vref := v;
  try
    let result = f () in
    vref := oldv;
    result
  with exn -> vref:=oldv; raise exn
  
let parse_typevars = ref false

let verbose = ref false
let verbose_interpret = ref false
let verbose_qsim = ref false
let verbose_qcalc = ref false
let verbose_simplify = ref false
let verbose_typecheck = ref false

let symbq = ref true

let verboseopts = [("all"              , verbose                  );
                   ("qcalc"            , verbose_qcalc            );
                   ("interpret"        , verbose_interpret        );
                   ("qsim"             , verbose_qsim             );
                   ("simplify"         , verbose_simplify         );
                   ("typecheck"        , verbose_typecheck        );
                  ] 
let setverbose s = (List.assoc s verboseopts) := true
