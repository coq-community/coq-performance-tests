.DEFAULT_GOAL := all

TIMED?=1
TIMING?=1

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

SKIP_FILES?=

SKIP_IF_NOT_NEW?=

ifneq (,$(filter 8.11%,$(COQ_VERSION)))
SKIP_FILES+=skip-8.11-older.txt $(SKIP_IF_NOT_NEW)
else
SKIP_IF_NOT_NEW+=skip-8.11-older.txt
ifneq (,$(filter 8.10%,$(COQ_VERSION)))
SKIP_FILES+=skip-8.10-older.txt $(SKIP_IF_NOT_NEW)
else
SKIP_IF_NOT_NEW+=skip-8.10-older.txt
ifneq (,$(filter 8.9%,$(COQ_VERSION)))
SKIP_FILES+=skip-8.9-older.txt $(SKIP_IF_NOT_NEW)
else
SKIP_IF_NOT_NEW+=skip-8.9-older.txt
ifneq (,$(filter 8.8%,$(COQ_VERSION)))
SKIP_FILES+=skip-8.8-older.txt $(SKIP_IF_NOT_NEW)
else
# new version, don't skip
endif
endif
endif
endif

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
