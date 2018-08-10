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

let set_arg aref v = aref:=v
;;
let opts = Arg.align 
             [("-chanbuf_limit"  , Arg.Int (set_arg chanbuf_limit), 
                    Printf.sprintf " channel buffer limit (-1 infinite, default %d)" !chanbuf_limit);
              ("-fancyvec"  , Arg.Bool (set_arg fancyvec), 
                    Printf.sprintf " fancy printing of qbit vectors (default %B)" !fancyvec);
              ("-interpret"  , Arg.Bool (set_arg interpret), 
                    Printf.sprintf " interpret the program (default %B)" !interpret);
              ("-matchcheck" , Arg.Bool (set_arg matchcheck), 
                    Printf.sprintf " matchcheck the program (default %B)" !matchcheck);
              ("-show_final"  , Arg.Set show_final, 
                    " show final state -- channels, stuck processes, qbit states");
              ("-symbq"  , Arg.Bool (set_arg symbq), 
                    Printf.sprintf " new unspecified qbits have symbolic values (default %B)" !symbq);
              ("-tryrotate"  , Arg.Set tryrotate, 
					" try rotating probability vectors when disentangling");
              ("-typereport"  , Arg.Set typereport, 
					" show fully typed program");
              ("-verbose", Arg.Symbol (List.map (fun (x,_) -> x) verboseopts, setverbose), 
					" verbose operation, various arguments, defaults false" ); 
             ]

let _ = Arg.parse opts (fun s -> files := s :: !files) usage

