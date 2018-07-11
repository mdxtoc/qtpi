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

    You should have received a copy of the GNU General Public License in file LICENSE
    along with Qtpi in the file LICENSE; if not, try http://www.gnu.org/licenses/gpl.html.
*)
 
let (<.>) f g a = f (g a)
let (<..>) f g a b = f (g a b)
let (<...>) f g a b c = f (g a b c)
let (<....>) f g a b c d = f (g a b c d)

let revargs f b a = f a b

let uncurry2 f (a,b) = f a b

let curry2 f a b = f (a,b)

let uncurry3 f (a,b,c) = f a b c

let curry3 f a b c = f (a,b,c)

let currypair a b = a,b

let id s = s

let ok s = true

let isAny fs v = List.exists (fun f -> f v) fs

let isAll fs v = List.for_all (fun f -> f v) fs

let (<&&>) f g x = f x && g x

let (<||>) f g x = f x || g x
