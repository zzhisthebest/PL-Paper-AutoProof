.PHONY: all clean
all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -f Makefile.coq clean
