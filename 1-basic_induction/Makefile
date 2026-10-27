DFILES = D.v 
PFILES = $(shell find P??.v)
EFILES = $(shell find E??_??.v)

POFILES = $(patsubst %.v,%.vo,$(PFILES))
EOFILES = $(patsubst %.v,%.vo,$(EFILES))

all: $(DFILES) $(PFILES) Makefile.coq
	$(MAKE) -f Makefile.coq $(POFILES)

check:
	bash ./check.sh

eval: $(DFILES) $(PFILES) $(EFILES) Makefile.coq check
	$(MAKE) -f Makefile.coq $(EOFILES)

submission:
	zip submission.zip P??.v

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq

Makefile.coq: Makefile _CoqProject $(PFILES) $(EFILES)
	coq_makefile -f _CoqProject -o Makefile.coq
