.DEFAULT_GOAL := coq

COMPONENTS := src PerformanceExperiments

.PHONY: $(COMPONENTS)
$(COMPONENTS):
	+$(MAKE) -C $@

.PHONY: coq
coq: $(COMPONENTS)

define make_delegate_target
.PHONY: $(1)
$(1): $(addprefix $(1)-,$(COMPONENTS))

.PHONY: $(addprefix $(1)-,$(COMPONENTS))
$(addprefix $(1)-,$(COMPONENTS)) : $(1)-% :
	+$(MAKE) -C $$* $(1)
endef

$(eval $(call make_delegate_target,validate))
$(eval $(call make_delegate_target,make-pretty-timed))
$(eval $(call make_delegate_target,print-pretty-timed))
$(eval $(call make_delegate_target,install))
$(eval $(call make_delegate_target,clean))

.PHONY: perf
perf: | PerformanceExperiments
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-Sanity perf-SuperFast perf-Fast
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-csv

.PHONY: perf-lite
perf-lite: | PerformanceExperiments
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-Sanity perf-SuperFast
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-csv

.PHONY: install-perf
install-perf:
	+$(MAKE) --no-print-directory -C PerformanceExperiments install-perf-Sanity install-perf-SuperFast install-perf-Fast

.PHONY: install-perf-lite
install-perf-lite:
	+$(MAKE) --no-print-directory -C PerformanceExperiments install-perf-Sanity install-perf-SuperFast

.PHONY: install-perf-Sanity
install-perf-Sanity:
	+$(MAKE) --no-print-directory -C PerformanceExperiments install-perf-Sanity

.PHONY: pdf
pdf:
	+$(MAKE) --no-print-directory -C plots

.PHONY: copy-pdf
copy-pdf:
	mkdir -p "$(OUTPUT)"
	cp -t "$(OUTPUT)" plots/all.pdf

.PHONY: doc
doc:
	+$(MAKE) --no-print-directory -C plots svg

.PHONY: copy-perf
copy-perf:
	mkdir -p "$(OUTPUT)"
	+$(MAKE) --no-print-directory -C PerformanceExperiments OUTPUT="$(abspath $(OUTPUT))" $@

.PHONY: copy-doc
copy-doc:
	mkdir -p "$(OUTPUT)"
	cp -t "$(OUTPUT)" plots/*.svg

include PerformanceExperiments/Makefile.variables
PERF_KINDS := $(addprefix perf-,$(SIZES))
.PHONY: $(PERF_KINDS)
$(PERF_KINDS): | PerformanceExperiments
	+$(MAKE) --no-print-directory -C PerformanceExperiments $@

.PHONY: update-README
update-README::
	etc/update-readme.sh $(sort $(KINDS) $(DISABLED_KINDS))
