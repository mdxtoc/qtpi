# This works with Ocaml [4.05.0, 4.06.0, 4.07.1, 4.08.1, 4.09.0] and zarith [1.7, 1.9.1]
# Now you also need sedlex (opam install sedlex). Works with version 1.2

Qtpi : *.ml *.mly
	ocamlbuild -use-ocamlfind qtpi.native

Qtpip : *.ml *.mly
	ocamlbuild -use-ocamlfind -tag debug -tag profile qtpi.native

clean :
	rm -fr _build *.native
	rm -f Qtpi

links :
	rm -f Qtpi
	ln -s qtpi.native Qtpi
