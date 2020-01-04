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

(* Assoc lists for typechecking and interpreting. Now straightforward, because there are no
   'monitor parameters'. Hurrah.
 *)
 
type 'a monenv = (name * 'a) list 

let (<@>)  = Listutils.(<@>)       
let (<@+>) = Listutils.(<@+>)       
let (<@->) = Listutils.(<@->)       
let (<@?>) = Listutils.(<@?>)       

(* just in case one day I want to use hash tables (or something else) as the global environment *)
let monenv_of_lg local global = local@global
let assoc_of_monenv env = env
let globalise env = env

let string_of_monassoc sep string_of_a = bracketed_string_of_list (string_of_pair string_of_name string_of_a sep)

let string_of_monenv = string_of_monassoc

let null = Listutils.null

let filter = List.filter 

(* let filterg f (local, usemon, mon, global) = local, usemon, mon, List.filter f global *)

let count n env = List.length (List.filter (fun (n',_) -> n=n') env)
  