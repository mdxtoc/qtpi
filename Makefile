# at present (2019 04) this works with Ocaml 4.06.0 and zarith 1.7

Qtpi : *.ml *.mly *.mll
	ocamlbuild -yaccflag -v  -use-ocamlfind qtpi.native

Qtpip : *.ml *.mly *.mll
	ocamlbuild -yaccflag -v  -use-ocamlfind -tag debug -tag profile qtpi.native

clean :
	rm -fr _build *.native
	rm -f Qtpi

links :
	rm -f Qtpi
	ln -s qtpi.native Qtpi
