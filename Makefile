# This works with Ocaml [4.05.0, 4.06.0, 4.07.1, 4.08.1, 4.09.0] and zarith [1.7, 1.9.1]
# Now you also need sedlex (opam install sedlex). Works with version 1.2

Qtpi : version *.ml *.mly
	ocamlbuild -use-ocamlfind qtpi.native

Qtpi.exe: version *.ml *.mly
	# this make is guaranteed to work: simpler ones don't
	make clean links Qtpi
	cp _build/qtpi.native Qtpi.exe
	
clean :
	rm -fr _build *.native
	rm -f Qtpi Qtpi.exe

links :
	rm -f Qtpi
	ln -s qtpi.native Qtpi

# use git for version
version:               
	echo let version=\"`./version.sh`\" >version.ml

zip :
	(rm -fr qtpi\ distrib; mkdir -p qtpi\ distrib; \
	 zip -r qtpi\ distrib/docs docs; \
	 zip -r qtpi\ distrib/examples BB84QKDcontrol.txt E92QKDcontrol.txt examples \
	) 
  
ziplinux :
	(make zip Qtpi; \
	 zip -r "qtpi distrib/Qtpi_Linux_`./version.sh`.zip" Qtpi \
	)
  
zipmacos :
	(make zip Qtpi; \
	 zip -d qtpi\ distrib/docs \*.DS_Store; \
	 zip -d qtpi\ distrib/examples \*.DS_Store; \
	 zip -r "qtpi distrib/Qtpi_Macos_`./version.sh`.zip" Qtpi \
	)

zipwindows : 
	(make zip Qtpi; \
	 zip -r "qtpi distrib/Qtpi_Windows_`./version.sh`.zip" Qtpi.exe; \
	 zip -r qtpi\ distrib/gmplib /cygdrive/c/Windows/System32/cyggmp-10.dll \
	)
