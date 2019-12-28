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
open Tupleutils
open Functionutils

(* Assoc lists for typechecking and interpreting.

   Because of process monitors, we need a multiple assoc-list. If usemon is true, we look in local,
   then mon, then global. If usemon is false, we look in local, then global.
   
   The 'local' assoc is for the main body of the process; the 'mon' is the monitor parameters;
   'global' is the parameters plus outside environment. Thus with usemon=false we get the env 
   for the main body of a process; with usemon=true we get the env for the monitor insertions.
 *)

(* I think this three-way split would allow the global environment to be something more efficient 
   than an assoc list. The local/mon split allows the monitor parameters to be always available
   to the monitor process: rebinding them in the body has no effect. The local assoc doesn't 
   include the parameters; the monenv just has the monitor parameters; global has the non-monitor
   parameters and the rest of the world. (It says that above, too.)
 *)
 
type 'a monenv = (name * 'a) list * bool * (name * 'a) list * (name * 'a) list

let (<%@>)  = Listutils.(<@>)       
let (<%@+>) = Listutils.(<@+>)       
let (<%@->) = Listutils.(<@->)       
let (<%@?>) = Listutils.(<@?>)       

let (<@>)  (local, usemon, mon, global) n = try local<%@>n
                                            with Not_found -> try if usemon then mon<%@>n else raise Not_found
                                                              with Not_found -> global<%@>n
let (<@+>) (local, usemon, mon, global) n = local<%@+>n, usemon, mon, global      
let (<@->) (local, usemon, mon, global) n = local<%@->n, usemon, mon, global       
let (<@?>) cxt                          n = try ignore (cxt<@>n); true with Not_found -> false     

let monenv_of_assoc assoc = [],false,[],assoc
let monenv_of_lmg local mon global = local,false,mon,global

let menv (local, usemon, mon, global) = local, true, mon, global
let assoc_of_monenv (local, usemon, mon, global) = local@(if usemon then mon else [])@global

let globalise env = monenv_of_assoc (assoc_of_monenv env)

let string_of_monassoc sep string_of_a = bracketed_string_of_list (string_of_pair string_of_name string_of_a sep)

let string_of_monenv sep string_of_a (local, usemon, mon, global) = 
   let soa = string_of_monassoc sep string_of_a in
   Printf.sprintf "(%s,%B,%s,%s)" (soa local) usemon (soa mon) (soa global)

let null (local, usemon, mon, global) = null local && (not usemon || null mon) && null global

let filter f (local, usemon, mon, global) = List.filter f local, usemon, List.filter f mon, List.filter f global

let filterg f (local, usemon, mon, global) = local, usemon, mon, List.filter f global

let count n (local, usemon, mon, global) =
  let c n e = List.length (List.filter (fun (n',_) -> n=n') e) in
  c n local + (if usemon then c n mon else 0) + c n global
  