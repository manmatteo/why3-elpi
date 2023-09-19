WHY3LIB=`~/repo/why3/bin/why3 --print-libdir`/why3

OCAMLARGS=-linkpkg -package elpi -package re -verbose -w A-4-9-41-42-44-45-52@5@8@14@48@50 -safe-string -keep-locs -bin-annot -dtypes -g -thread -dontlink "menhirLib re unix num dynlink zip sexplib sexplib.num ppx_sexp_conv"

all: bin/why3_elpi.cmxs
%.cmxs: %.cmx
	ocamlfind ocamlopt ${OCAMLARGS} -I ${WHY3LIB} -I bin  -linkpkg -shared -o $@ $<

%.cmx: %.ml %.cmi
	ocamlfind ocamlopt -c ${OCAMLARGS} -I ${WHY3LIB} -I bin  $<

%.cmi: %.mli
	ocamlfind ocamlc -c ${OCAMLARGS} -I ${WHY3LIB} -I bin  $<

.PHONY: clean
clean:
	rm -f bin/*.cm* bin/*.o bin/*.annot
