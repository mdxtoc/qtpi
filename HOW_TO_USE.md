# Get Me

from [GitHub](https://github.com/mdxtoc/qtpi): use the "Clone or download" button. There are also some binary releases -- note that you need to download GNU gmp as well as qtpi (see release documentation).

# Build Me

  You will need OCaml (in January 2020 I'm building with version 4.09.0), ocamlbuild and ocamlfind. On Windows you need cygwin. On any operating system you need OCaml's zarith which needs GNU gmp. If you use OCaml's wonderful `opam` to manage your OCaml downloads it can be persuaded to sort it out for you. Otherwise on MacOS `brew install gmp`; on Windows get libgmp from Cygwin and copy it into `C:\\Windows32`; on Linux `apt install libgmp10`
  
  You will need OCaml's sedlex: `opam install sedlex` and menhir: `opam install menhir`
  
  Then, in a terminal/console

        make clean
        make links
        make Qtpi

  # Try Me

        ./Qtpi examples/??.qtp
        
  Lots of examples to try. See [the BBEdit worksheet](https://github.com/mdxtoc/qtpi/blob/master/Qtpi.worksheet) for how to run them and perhaps some hints about what they are supposed to do.
  
# Documentation

  See the 'docs' directory. Not always quite up to date about the state of the language (sorry).
