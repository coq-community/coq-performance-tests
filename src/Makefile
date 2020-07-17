.DEFAULT_GOAL := all

TIMED?=1
TIMING?=1

export TIMED
export TIMING

ifneq ($(wildcard ../.git),)
FILE_FINDER := git ls-files
else
$(warning Not a git clone, using find instead)
FILE_FINDER := find -name
endif

_CoqProject::
	@(echo "-Q . CoqPerformanceTests"; $(FILE_FINDER) "*.v") > $@

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@
