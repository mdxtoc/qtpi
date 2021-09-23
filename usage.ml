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

let print_version () = Printf.printf "qtpi version %s\n" Version.version

let set_arg aref v = aref:=v
;;
let opts = Arg.align 
             [("-chanbuf_limit"  , Arg.Int (set_arg chanbuf_limit), 
                    Printf.sprintf " channel buffer limit (-1 infinite, default %d)" !chanbuf_limit);
              ("-checkrandombias"  , Arg.Set checkrandombias, 
                    " print out simple stats on random choices");
              ("-complexunknowns" , Arg.Bool (set_arg complexunknowns), 
                    Printf.sprintf " unnown qbit amplitudes (a0, b0 etc.) stand for complex numbers, not reals (default %B)" !complexunknowns);
              (* ("-detectdisposes"  , Arg.Bool (set_arg detectdisposes), 
                    Printf.sprintf " binding a measured qbit's value disposes the qbit (default %B)" !detectdisposes); *)
              ("-fancynum"  , Arg.Bool (set_arg fancynum), 
                    Printf.sprintf " fancy printing of symbolic numbers (default %B)" !fancynum);
              ("-fancyvec"  , Arg.Bool (set_arg fancyvec), 
                    Printf.sprintf " fancy printing of qbit vectors (default %B)" !fancyvec);
              ("-func_matrices" , Arg.Bool (set_arg func_matrices), 
                    Printf.sprintf " some matrices, such as I⊗⊗n and H⊗⊗n, are represented by functions (default %B)" !func_matrices);
              ("-interpret"  , Arg.Bool (set_arg interpret), 
                    Printf.sprintf " interpret the program (default %B)" !interpret);
              ("-matchcheck" , Arg.Bool (set_arg matchcheck), 
                    Printf.sprintf " matchcheck the program (default %B)" !matchcheck);
              ("-measuredestroys" , Arg.Bool (set_arg measuredestroys), 
                    Printf.sprintf " measurement destroys a qbit (default %B)" !measuredestroys);
              ("-memoise" , Arg.Bool (set_arg memoise), 
                    Printf.sprintf " memoise calculator operations mult and sum (default %B)" !memoise);
              ("-show_final"  , Arg.Set show_final, 
                    " show final state -- channels, stuck processes, qbit states");
              ("-showabvalues"  , Arg.Bool (set_arg showabvalues), 
					 Printf.sprintf " show actual value of a_i, b_i in random qbit choice (default %B)" !showabvalues);
              ("-showsymbolicgate"  , Arg.Bool (set_arg showsymbolicgate), 
					 Printf.sprintf " `show' displays symbolic name of gate (I, H, X etc.) where possible (default %B)" !showsymbolicgate);
              ("-symbq"  , Arg.Bool (set_arg symbq), 
                    Printf.sprintf " new unspecified qbits have symbolic values (default %B)" !symbq);
              (* ("-pstep"     , Arg.Set pstep, 
					" step through protocol execution"); *)
              ("-resourcecheck"  , Arg.Bool (set_arg resourcecheck), 
					 Printf.sprintf " static resource check of correct use of qbits (default %B)" !Settings.resourcecheck);
              ("-stepcount"  , Arg.Set showstepcount, 
					 Printf.sprintf " show interpreter stepcount");
              ("-trace"  , Arg.Set traceevents, 
					" show trace of quantum events, messages, disposal, at end of execution");
              ("-traceId"     , Arg.Set traceevents, 
					" show trace of process ids (probably unnecessary), at end of execution");
              ("-try_rotate"  , Arg.Bool (set_arg try_rotate), 
					 Printf.sprintf " when splitting state, try every qbit (default %B)" !Settings.try_rotate);
              ("-trydiag"  , Arg.Bool (set_arg trydiag), 
					 Printf.sprintf " use diagonal matrix optimisation in calculations (default %B)" !Settings.trydiag);
              ("-typereport"  , Arg.Set typereport, 
					" show fully typed program");
              ("-verbose", Arg.Symbol (List.map (fun (x,_) -> x) verboseopts, setverbose), 
					" verbose operation, various arguments, defaults false" ); 
              ("-version", Arg.Unit print_version, 
					" show version number" ); 
             ]

let _ = Arg.parse opts (fun s -> files := s :: !files) usage

