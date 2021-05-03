

all: coq

coq: Lambdagc.mk
	rm -rf Lambdagc
	make -f Lambdagc.mk

Lambdagc.mk:
	coq_makefile -f _CoqProject -o Lambdagc.mk

clean: Lambdagc.mk
	make -f Lambdagc.mk clean
	rm -f Lambdagc.mk*
	rm -f *.cmi *.cmo coqsplit *_full* *_sol* *.v-e
