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
open Vmg

type event =
  | EVMessage of chan * name * name * value
  | EVInput of name * value
  | EVOutput of name * value
  | EVDispose of name * value
  | EVGate of name * string list * gate * string list
  | EVMeasure of name * qbit list * gate * value list * string list
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
                                                                           (string_of_gate g)
                                                                           (soqs ss')
  | EVMeasure (pn, qs, g, vs, aqs)  
                                -> Printf.sprintf "%s: %s -/- %s; result %s%s" 
                                     (string_of_name pn)
                                     (string_of_qbits qs)
                                     (if g=g_I then "" else ("[" ^ string_of_gate g ^ "]"))
                                     (string_of_multi string_of_value vs)
                                     (if null aqs then "" else " and " ^ soqs aqs)
                                                                           
  | EVChangeId (pn, npns)       -> Printf.sprintf "%s morphs into %s" (string_of_name pn)
                                                                      (string_of_list string_of_name ", " npns)

(* tev is trace eval. Tries not to repeat values in the list qs *)                                                                 
let tev qs = 
  let rec tqs prevqs qs =
    match qs with 
    | q::qs -> (try let prevq = List.find (fun q' -> Qsim.qval q=Qsim.qval q') prevqs in
                    Printf.sprintf "%s=%s" (string_of_qbit q) (string_of_qbit prevq)
                with Not_found -> 
                    Printf.sprintf "%s:%s" (string_of_qbit q) (Qsim.string_of_qval (Qsim.qval q))
               ) :: tqs (prevqs@[q]) qs (* why append??? *)
    | _     -> []
  in
  tqs [] qs

let stored_trace = (ref [] : event list ref)

let show_trace () = 
  List.iter (fun e -> Printf.printf "%s\n" (string_of_event e)) (List.rev !stored_trace)
                
let trace e = stored_trace := e::!stored_trace
