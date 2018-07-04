Qtpi : *.ml *.mly *.mll
	ocamlbuild -yaccflag -v  qtpi.native
#	ocamlbuild -yaccflag -v -lib `pwd`/z3/build/api/ml/z3 -lflags -ccopt,-L`pwd`/z3/build/api/ml -lib unix -lib str arsenic.native
#	ocamlbuild -yaccflag -v -lib unix -lib str arsenic.native

clean :
	rm -fr _build *.native
	rm -f Qtpi

links :
	rm -f Qtpi
	ln -s qtpi.native Qtpi
