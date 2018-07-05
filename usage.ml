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

open Settings

let progname = Sys.argv.(0)
let files = ref []
let usage = "Usage: " ^ progname ^ " [options]* filename filename ..."

let set_bool bref b = bref:=b

let opts = Arg.align 
             [("-symbq"  , Arg.Bool (set_bool symbq), 
                    Printf.sprintf " new qbits have symbolic values (default %B)" !symbq);
              ("-verbose", Arg.Symbol (List.map (fun (x,_) -> x) verboseopts, setverbose), 
                   " verbose operation, various arguments, defaults false" ); 
             ]

let _ = Arg.parse opts (fun s -> files := s :: !files) usage

