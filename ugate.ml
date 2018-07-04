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

open Expr

type ugate =
  | GH
  | GI
  | GX
  | GCnot
  | GPhi of expr
  | GCond of expr * ugate * ugate

let rec string_of_ugate = function
  | GH              -> "_H"  
  | GI              -> "_I"
  | GX              -> "_X"
  | GCnot           -> "_CNot"
  | GPhi (e)        -> Printf.sprintf "_Phi(%s)" (string_of_expr e)
  | GCond (e,u1,u2) -> Printf.sprintf "if %s then %s else %s fi"
                                      (string_of_expr e)
                                      (string_of_ugate u1)
                                      (string_of_ugate u2)
