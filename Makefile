.DEFAULT_GOAL := all

_CoqProject:
	@(echo "-Q . CoqPerformanceTests"; git ls-files "*.v") > $@

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@
