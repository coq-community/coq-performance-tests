# coq-performance-tests
[![CI (Coq)](https://github.com/coq-community/coq-performance-tests/workflows/CI%20(Coq)/badge.svg)](https://github.com/coq-community/coq-performance-tests/actions?query=branch%3Amaster+workflow%3A%22CI+%28Coq%29%22)

A library of Coq source files testing for performance regressions on Coq

## Contributing

Please add tests to this repository.

Each test should go in its own .v file in `src/`, and each .v file should be
targeted to take around 1 minute, so that all tests get roughly equal
weight.

## PerformanceExperiments

The [`PerformanceExperiments`](./PerformanceExperiments/) folder contains a number of tests based on a [test harness file](./PerformanceExperiments/Harness.v) which allow automatic generation of plots, as displayed below.
The plots are updated on each run of GitHub Actions.
To contribute to this folder, please add your test to [`Makefile.variables.kinds`](./PerformanceExperiments/Makefile.variables.kinds) and follow the format of the existing tests.
You can use [`gen-listing.sh`](./PerformanceExperiments/gen-listing.sh) to generate the tables for this README.

- [`n_polymorphic_universes`](./PerformanceExperiments/n_polymorphic_universes.v)

  master | 8.11.2 | 8.10.2 | 8.9.1 | 8.8.2
  --|--|--|--|--
  <img src="https://coq-community.github.io/coq-performance-tests/master/n-polymorphic-universes.svg" height=100px /> | <img src="https://coq-community.github.io/coq-performance-tests/8.11.2/n-polymorphic-universes.svg" height=100px /> | <img src="https://coq-community.github.io/coq-performance-tests/8.10.2/n-polymorphic-universes.svg" height=100px /> | <img src="https://coq-community.github.io/coq-performance-tests/8.9.1/n-polymorphic-universes.svg" height=100px /> | <img src="https://coq-community.github.io/coq-performance-tests/8.8.2/n-polymorphic-universes.svg" height=100px />

- [`pattern`](./PerformanceExperiments/pattern.v)

  master | 8.11.2 | 8.10.2 | 8.9.1 | 8.8.2
  --|--|--|--|--
  <img src="https://coq-community.github.io/coq-performance-tests/master/pattern.svg" height=100px /> | <img src="https://coq-community.github.io/coq-performance-tests/8.11.2/pattern.svg" height=100px /> | <img src="https://coq-community.github.io/coq-performance-tests/8.10.2/pattern.svg" height=100px /> | <img src="https://coq-community.github.io/coq-performance-tests/8.9.1/pattern.svg" height=100px /> | <img src="https://coq-community.github.io/coq-performance-tests/8.8.2/pattern.svg" height=100px />
