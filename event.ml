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
open Type
open Functionutils
open Settings

type tv = Type._type * Vt.vt
type event =
  | EVMessage of chan * name * name * tv
  | EVInput of name * tv
  | EVOutput of name * tv
  | EVCreate of name * bool * string list (* bool is plural *)
  | EVDispose of name * tv
  | EVGate of name * string list * gate * string list
  | EVMeasure of name * string list * gate * bool list * string list
  | EVChangeId of name * name list
  
let soqs = function
  | [s] -> s
  | ss  -> Printf.sprintf "(%s)" (String.concat "," ss)

let string_of_event = function
  | EVMessage (c,pout,pin,(t,v))    -> Printf.sprintf "%s: %s -> %s %s" (short_string_of_chan t c)
                                                                        (string_of_name pout)
                                                                        (string_of_name pin)
                                                                        (string_of_value t v)
  | EVInput (pn,(t,v))              -> Printf.sprintf "%s inputs %s" (string_of_name pn) (string_of_value t v)
  | EVOutput (pn,(t,v))             -> Printf.sprintf "%s outputs %s" (string_of_name pn) (string_of_value t v)
  | EVCreate (pn,plural,ss)        -> Printf.sprintf "%s creates %s" (string_of_name pn) (if plural then bracketed_string_of_list id ss
                                                                                                     else List.hd ss
                                                                                         )
  | EVDispose (pn,(t,v))            -> Printf.sprintf "%s disposes %s" (string_of_name pn) (string_of_value t v)
  | EVGate (pn, ss, g, ss')         -> Printf.sprintf "%s %s >> %s; result %s" (string_of_name pn)
                                                                               (soqs ss)
                                                                               (Value.string_of_gate g)
                                                                               (soqs ss')
  | EVMeasure (pn, qs, g, bs, aqs)  
                                -> Printf.sprintf "%s: %s ⌢̸ %s; result %s%s" 
                                     (string_of_name pn)
                                     (match qs with [q] -> q | _ -> soqs qs)
                                     (if g=g_I then "" else ("[" ^ string_of_gate g ^ "]"))
                                     (string_of_multi string_of_bit bs)
                                     (if null aqs then "" else " and " ^ soqs aqs)
                                                                           
  | EVChangeId (pn, npns)       -> Printf.sprintf "%s morphs into %s" (string_of_name pn)
                                                                      (string_of_list string_of_name ", " npns)

(* tev is trace eval. Tries not to repeat values in the list qs *)                                                                 
let tev qs = 
  let rec tqs prevqs qs =
    match qs with 
    | q::qs -> (try let prevq = List.find (fun q' -> Qsim.qval q=Qsim.qval q') prevqs in
                    Printf.sprintf "%s=%s" (string_of_qubit q) (string_of_qubit prevq)
                with Not_found -> 
                    Printf.sprintf "%s:%s" (string_of_qubit q) (Qsim.string_of_qval (Qsim.qsort (Qsim.qval q)))
               ) :: tqs (prevqs@[q]) qs (* why append??? *)
    | _     -> []
  in
  tqs [] qs

let stored_trace = (ref [] : event list ref)

let show_trace () = 
  Printf.printf "\nEvent Trace:\n\n";
  List.iter (fun e -> Printf.printf "%s\n\n" (string_of_event e)) (List.rev !stored_trace);
  Printf.printf "\n"
                
let trace e = if !verbose_trace then Printf.printf "%s\n" (string_of_event e);
              if !traceevents then stored_trace := e::!stored_trace
