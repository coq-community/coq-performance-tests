.DEFAULT_GOAL := all

TIMED?=1
TIMING?=1

export TIMED
export TIMING

_CoqProject::
	@(echo "-Q . CoqPerformanceTests"; git ls-files "*.v") > $@

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@
