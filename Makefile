Qtpi : *.ml *.mly *.mll
	ocamlbuild -yaccflag -v  -use-ocamlfind qtpi.native

clean :
	rm -fr _build *.native
	rm -f Qtpi

links :
	rm -f Qtpi
	ln -s qtpi.native Qtpi
