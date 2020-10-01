# This works with Ocaml [4.05.0, 4.06.0, 4.07.1, 4.08.1, 4.09.0] and zarith [1.7, 1.9.1]
# Now you also need sedlex (opam install sedlex). Works with version 1.2

Qtpi : *.ml *.mly
	ocamlbuild -use-ocamlfind qtpi.native

Qtpip : *.ml *.mly
	ocamlbuild -use-ocamlfind -tag debug qtpi.native

clean :
	rm -fr _build *.native
	rm -f Qtpi

links :
	rm -f Qtpi
	ln -s qtpi.native Qtpi

zip :
	(mkdir -p qtpi\ distrib; \
	 zip -r qtpi\ distrib/docs docs; \
	 zip -r qtpi\ distrib/examples BB84QKDcontrol.txt E92QKDcontrol.txt examples \
	) 
  
ziplinux :
	(make zip Qtpi; \
	 zip -r qtpi\ distrib/Qtpi_Linux Qtpi \
	)
  
zipmacos :
	(make zip Qtpi; \
	 zip -d qtpi\ distrib/docs \*.DS_Store; \
	 zip -d qtpi\ distrib/examples \*.DS_Store; \
	 zip -r qtpi\ distrib/Qtpi_Macos Qtpi \
	)

zipwindows :
	(make zip Qtpi; \
	 zip -r qtpi\ distrib/Qtpi_Windows Qtpi.exe \
	)
