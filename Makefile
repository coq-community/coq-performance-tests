.DEFAULT_GOAL := coq

COMPONENTS := src PerformanceExperiments

.PHONY: $(COMPONENTS)
$(COMPONENTS):
	+$(MAKE) -C $@

.PHONY: coq
coq: $(COMPONENTS)

.PHONY: install clean
install clean:
	+$(MAKE) -C src $@
	+$(MAKE) -C PerformanceExperiments $@

.PHONY: perf
perf:
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-Sanity perf-SuperFast perf-Fast
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-csv

.PHONY: install-perf
install-perf:
	+$(MAKE) --no-print-directory -C PerformanceExperiments install-perf-Sanity install-perf-SuperFast install-perf-Fast

.PHONY: install-perf-Sanity
install-perf-Sanity:
	+$(MAKE) --no-print-directory -C PerformanceExperiments install-perf-Sanity

.PHONY: pdf
pdf:
	+$(MAKE) --no-print-directory -C plots

.PHONY: copy-pdf
copy-pdf:
	mkdir -p $(OUTPUT)
	cp -t $(OUTPUT) plots/all.pdf

.PHONY: doc
doc:
	+$(MAKE) --no-print-directory -C plots svg

.PHONY: copy-perf
copy-perf:
	+$(MAKE) --no-print-directory -C PerformanceExperiments OUTPUT="$(abspath $(OUTPUT))" $@

.PHONY: copy-doc
copy-doc:
	cp -t $(OUTPUT) plots/*.svg

include PerformanceExperiments/Makefile.variables
PERF_KINDS := $(addprefix perf-,$(SIZES))
.PHONY: $(PERF_KINDS)
$(PERF_KINDS):
	+$(MAKE) --no-print-directory -C PerformanceExperiments $@
