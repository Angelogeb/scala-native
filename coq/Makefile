.DEFAULT_GOAL := all

Makefile:;
_CoqProject:;

%: Makefile.coq
	@$(MAKE) -f Makefile.coq $@

clean: cleanall
	$(RM) Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	@coq_makefile -f _CoqProject -o $@

.PHONY: default clean
