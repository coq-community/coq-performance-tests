.DEFAULT_GOAL := all

mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
mkfile_dir := $(dir $(mkfile_path))

TIMED?=1
TIMING?=1
PYTHON?=python

export TIMED
export TIMING

SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

ifneq ($(wildcard ../.git),)
FILE_FINDER := git ls-files
else
$(warning Not a git clone, using find instead)
FILE_FINDER := find -name
endif

COQ_VERSION_PREFIX = The Coq Proof Assistant, version
COQ_VERSION_FULL := $(subst $(COQ_VERSION_PREFIX),,$(shell $(COQBIN)coqc --version 2>/dev/null))
COQ_VERSION := $(firstword $(COQ_VERSION_FULL))

include $(mkfile_dir)skip-old.mk

$(mkfile_dir)skip-old.mk: generate-skip.py Makefile
	rm -f $@
	$(PYTHON) $< > $@
	chmod a-w $@

ifneq (,$(SKIP_FILES))
GREP_INVOCATION:=| grep -v $(foreach f,$(SKIP_FILES),-f $(f))
else
GREP_INVOCATION:=
endif

WARNINGS := -deprecated-hint-rewrite-without-locality,-deprecated-typeclasses-transparency-without-locality

_CoqProject::
	$(HIDE)(echo "-Q . CoqPerformanceTests"; echo '-arg -w -arg $(WARNINGS)'; ($(FILE_FINDER) "*.v" $(GREP_INVOCATION))) > $@

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@
