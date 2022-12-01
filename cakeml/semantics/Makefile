GENERATOR=../../generator


all: demo

coq.ml print_coq.ml: $(GENERATOR)/coq.ml $(GENERATOR)/print_coq.ml
	cp $(GENERATOR)/$@ $@

demo: demo.vo

demo.ml:
	cp demo_sample.ml $@

demo.vo: Prelude.vo

%.vo: %.v
	coqc $<

demo.v: demo.byte demo.ml 
	./demo.byte

demo.byte: demo.ml coq.ml print_coq.ml coq_from_hol.ml
	ocamlbuild -package pprint $@

clean:
	rm -Rf _build
	rm -f coq.ml print_coq.ml
	rm -f demo.v *.vo
