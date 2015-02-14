COQC=coqc

all: coq

coq:
	$(COQC) Basics.v Induction.v Lists.v Poly.v

clean:
	rm *.vo *.glob
