# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := clean cleanall
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := \
	Makefile \
	Makefile.variables \
	Makefile.characters \
	Makefile.coq-versions \
	Makefile.coq-versions-lite \
	Makefile.coq-versions-files \
	Makefile.timing

.DEFAULT_GOAL := all

include Makefile.characters
include Makefile.timing
include Makefile.coq-versions-lite
include Makefile.variables

all:: invoke-coqmakefile
.PHONY: all

WARNINGS:=-notation-overridden

ifneq ($(wildcard ../.git),)
FILE_FINDER := git ls-files
else
$(warning Not a git clone, using find instead)
FILE_FINDER := find -name
endif
SORT_COQPROJECT = sed 's,^\./,,g; s,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq
OLD_COQPROJECT_CONTENTS:=$(shell cat _CoqProject 2>/dev/null)
COQPROJECT_CONTENTS_CMD:=(echo '-R . $(PERF_LIB)'; echo '-arg -w -arg $(WARNINGS)'; ((echo '$(COMPATIBILITY_FILES) $(filter-out $(DISABLED_FILES),$(shell $(FILE_FINDER) "*.v"))' | tr ' ' '\n') | $(SORT_COQPROJECT)))
COQPROJECT_CONTENTS:=$(shell $(COQPROJECT_CONTENTS_CMD))
ifneq ($(OLD_COQPROJECT_CONTENTS),$(COQPROJECT_CONTENTS))
_CoqProject::
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)$(COQPROJECT_CONTENTS_CMD) > _CoqProject
else
_CoqProject: ;
endif

Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

cleanall clean:: Makefile.coq
	+$(MAKE) -f Makefile.coq $@
	rm -f Makefile.coq Makefile.coq.conf
.PHONY: cleanall clean

ifeq ($(MAKECMDGOALS),)
invoke-coqmakefile: Makefile.coq
	@+$(MAKE) --no-print-directory -f Makefile.coq
else
ifneq ($(filter-out $(KNOWNFILES) $(KNOWNTARGETS),$(MAKECMDGOALS)),)
invoke-coqmakefile: Makefile.coq
	@+$(MAKE) --no-print-directory -f Makefile.coq $(filter-out $(KNOWNFILES) $(KNOWNTARGETS),$(MAKECMDGOALS))
else
invoke-coqmakefile: Makefile.coq
	@true
endif
endif
.PHONY: invoke-coqmakefile

$(KNOWNFILES): ;

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
