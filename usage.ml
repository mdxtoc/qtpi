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

open Settings

let progname = Sys.argv.(0)
let files = ref []
let usage = "Usage: " ^ progname ^ " [options]* filename filename ..."
let ok_nofiles = ref false

let print_version () = Printf.printf "qtpi version %s\n" Version.version; ok_nofiles := true

let set_arg aref v = aref:=v
;;
let opts = Arg.align 
             [("-chanbuf_limit"     , Arg.Int (set_arg chanbuf_limit), 
                    Printf.sprintf " channel buffer limit (-1 infinite, default %d)" !chanbuf_limit);
              ("-checkrandombias"   , Arg.Set checkrandombias, 
                    " print out simple stats on random choices");
              ("-complexcombine"    , Arg.Bool (set_arg complexcombine),
                     Printf.sprintf " combine a?𝕣 and a?𝕚 when printing numbers (default %B)" !Settings.complexcombine);
              ("-factorbraket"      , Arg.Bool (set_arg factorbraket), 
                    Printf.sprintf " factorise bra/kets when printing (default %B)" !factorbraket);
              ("-fancynum"          , Arg.Symbol (List.map (fun (x,_) -> x) fancynumopts, setfancynum), 
                    Printf.sprintf " fancy printing of symbolic numbers (default %s)" (decode_fancynum ()));
              ("-fancyvec"          , Arg.Bool (set_arg fancyvec), 
                    Printf.sprintf " fancy printing of qubit vectors (default %B)" !fancyvec);
              ("-func_matrices"     , Arg.Bool (set_arg func_matrices), 
                    Printf.sprintf " some matrices, such as I⊗⊗n and H⊗⊗n, are represented by functions (default %B)" !func_matrices);
              ("-gatingsimplifies"    , Arg.Bool (set_arg gatingsimplifies), 
                    Printf.sprintf " after gating, simplify the resulting state when possible (default %B)" !gatingsimplifies);
              ("-interpret"         , Arg.Bool (set_arg interpret), 
                    Printf.sprintf " interpret the program (default %B)" !interpret);
              ("-matchcheck"        , Arg.Bool (set_arg matchcheck), 
                    Printf.sprintf " matchcheck the program (default %B)" !matchcheck);
              ("-measuredestroys"   , Arg.Bool (set_arg measuredestroys), 
                    Printf.sprintf " measurement destroys a qubit (default %B)" !measuredestroys);
              ("-memoise"           , Arg.Bool (set_arg memoise), 
                    Printf.sprintf " memoise calculator operations mult and sum (default %B)" !memoise);
              ("-resourcecheck"     , Arg.Bool (set_arg resourcecheck), 
					 Printf.sprintf " static resource check of correct use of qubits (default %B)" !Settings.resourcecheck);
              ("-rootcombine"       , Arg.Bool (set_arg rootcombine),
                     Printf.sprintf " combine number and square roots when printing products (default %B)" !Settings.rootcombine);
              ("-runbraket"         , Arg.Bool (set_arg runbraket), 
                    Printf.sprintf " show runs -- e.g. |00>+...+|10> -- when printing vectors (default %B)" !runbraket);
              ("-show_final"        , Arg.Set show_final, 
                    " show final state -- channels, stuck processes, qubit states");
              ("-showabvalues"      , Arg.Bool (set_arg showabvalues), 
					 Printf.sprintf " show actual value of a_i, b_i in random qubit choice (default %B)" !showabvalues);
              ("-showdensematrices" , Arg.Bool (set_arg showdensematrices), 
                    Printf.sprintf " show matrices in dense form, not sparse or diag (default %B)" !showdensematrices); 
              ("-showsymbolicgate"  , Arg.Bool (set_arg showsymbolicgate), 
					 Printf.sprintf " `show' displays symbolic name of gate (I, H, X etc.) where possible (default %B)" !showsymbolicgate);
              ("-showqsimplifies"    , Arg.Bool (set_arg showqsimplifies), 
                    Printf.sprintf " showq shows simplified multi-qubit states when possible (default %B)" !showqsimplifies);
              ("-showunknownparts"  , Arg.Bool (set_arg showunknownparts), 
                    Printf.sprintf " unnowns shown with real (𝕣) and imaginary (𝕚) parts (default %B)" !showunknownparts);
              ("-showstepcount"     , Arg.Set showstepcount, 
					 Printf.sprintf " show interpreter stepcount");
              ("-splitplurals"      , Arg.Bool (set_arg splitplurals), 
					 Printf.sprintf " try to separate gated plurals from rest of state (default %B)" !splitplurals);
              ("-symbolic_ht"       , Arg.Bool (set_arg symbolic_ht), 
					 Printf.sprintf " print r(1/2) as h, r(1/3) as t (default %B)" !symbolic_ht);
              ("-symbq"             , Arg.Bool (set_arg symbq), 
                    Printf.sprintf " new unspecified qubits have symbolic values (default %B)" !symbq);
              (* ("-pstep"          , Arg.Set pstep, 
					" step through protocol execution"); *)
              ("-trace"             , Arg.Set traceevents, 
					" show trace of quantum events, messages, disposal, at end of execution");
              ("-traceId"           , Arg.Set traceId, 
					" show trace of process ids (probably unnecessary), at end of execution");
              ("-trydiag"           , Arg.Bool (set_arg trydiag), 
					 Printf.sprintf " use diagonal matrix optimisation in calculations (default %B)" !Settings.trydiag);
              ("-typereport"        , Arg.Set typereport, 
					" show fully typed program");
              ("-usetestpoints"     , Arg.Bool (set_arg usetestpoints), 
					Printf.sprintf " execute testpoint code  (default %B)" !Settings.usetestpoints);
              ("-verbose"           , Arg.Symbol (List.map (fun (x,_) -> x) verboseopts, setverbose), 
					" verbose operation, various arguments, defaults false" ); 
              ("-version"           , Arg.Unit print_version, 
					" show version number" ); 
             ]

let _ = Arg.parse opts (fun s -> files := s :: !files) usage

