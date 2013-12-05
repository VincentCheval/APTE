OBJ = debug.cmx term.cmx distrib.cmx data.cmx

COMPILE = $(OBJ:%.cmx=%.mli) $(OBJ:%.cmx=%.ml) $(OBJ:%.cmx=%.cmi) $(OBJ)


# Starting Point

main: .depend $(COMPILE)
	@echo
	@echo The worker executable :
	@echo
	ocamlopt -o worker unix.cmxa $(OBJ) client.ml
	ocamlopt -o server unix.cmxa $(OBJ) server.ml
		
# Module

.SUFFIXES: .ml .mli .cmx .cmi

.mli.cmi: 
	ocamlopt -c $<

.ml.cmx: 
	ocamlopt -c $<

# Clean up

clean: 
	rm -f *~ *.cm[iox] *.o
	
# Dependencies 

.depend:
	ocamldep *.mli *.ml > .depend 
	
include .depend
