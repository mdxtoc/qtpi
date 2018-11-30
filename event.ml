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

open Name
open Listutils
open Value

type event =
  | EVMessage of chan * name * name * value
  | EVInput of name * value
  | EVOutput of name * value
  | EVDispose of name * value
  | EVGate of name * string list * ugv * string list
  | EVMeasure of name * string * ugv list * value * string list
  | EVChangeId of name * name list
  
let soqs = function
  | [s] -> s
  | ss  -> Printf.sprintf "(%s)" (String.concat "," ss)

let string_of_event = function
  | EVMessage (c,pout,pin,v)    -> Printf.sprintf "%s: %s -> %s %s" (short_string_of_value (VChan c))
                                                                    (string_of_name pout)
                                                                    (string_of_name pin)
                                                                    (string_of_value v)
  | EVInput (pn,v)              -> Printf.sprintf "%s inputs %s" (string_of_name pn) (string_of_value v)
  | EVOutput (pn,v)             -> Printf.sprintf "%s outputs %s" (string_of_name pn) (string_of_value v)
  | EVDispose (pn,v)            -> Printf.sprintf "%s disposes %s" (string_of_name pn) (string_of_value v)
  | EVGate (pn, ss, g, ss')     -> Printf.sprintf "%s %s >> %s; result %s" (string_of_name pn)
                                                                           (soqs ss)
                                                                           (string_of_ugv g)
                                                                           (soqs ss')
  | EVMeasure (pn, qv, gvs, v, aqs)  
                                -> let sogs = function
                                     | []      
                                     | [GateI] -> ""
                                     | gs      -> " " ^ bracketed_string_of_list string_of_ugv gs
                                   in
                                   Printf.sprintf "%s: %s =?%s; result %s%s" (string_of_name pn)
                                                                           qv
                                                                           (sogs gvs)
                                                                           (string_of_value v)
                                                                           (if null aqs then "" else " and " ^ soqs aqs)
                                                                           
  | EVChangeId (pn, npns)       -> Printf.sprintf "%s morphs into %s" (string_of_name pn)
                                                                      (string_of_list string_of_name ", " npns)
                                                                 
let tev q = Printf.sprintf "%s:%s" (string_of_qbit q) (Qsim.string_of_qval (Qsim.qval q))

let stored_trace = (ref [] : event list ref)

let string_of_trace () = 
  String.concat "\n"
                (List.map string_of_event (List.rev !stored_trace))
                
let trace e = stored_trace := e::!stored_trace
