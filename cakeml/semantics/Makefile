GENERATOR=../../generator


all: demo

coq.ml:
	ln -s $(GENERATOR)/coq.ml coq.ml

print_coq.ml:
	ln -s $(GENERATOR)/print_coq.ml print_coq.ml

demo: Demo.vo Demo_proofs.vo

demo.ml:
	ln -s demo_sample.ml $@

Demo.vo: Prelude.vo
Demo_proofs.vo: Demo_obligations.vo Demo.vo

%.vo: %.v
	coqc $<

Demo.v Demo_obligations.v: demo.byte demo.ml 
	./demo.byte

demo.byte: demo.ml coq.ml print_coq.ml coq_from_hol.ml
	ocamlbuild -package pprint $@

clean:
	rm -Rf _build
	rm -f coq.ml print_coq.ml
	rm -f Demo.v Demo_obligations.v *.vo



# --DEPRECATED
# coq.ml print_coq.ml: $(GENERATOR)/coq.ml $(GENERATOR)/print_coq.ml
#	cp $(GENERATOR)/$@ $@
#up:
#	cp demo_sample.ml demo.ml
#	$(MAKE) all
