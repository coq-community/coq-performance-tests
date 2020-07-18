#!/usr/bin/env bash

# Pass this script a list of file names, and it'll print the relevant
# lines for README.md to display things

stems="$@"
stems="$(echo "$stems" | tr ' ' '\n' | sed 's/\.v$//g' | tr '\n' ' ')"
extra_bar=""
extra_bar_space=""
coq_versions="master 8.11.2 8.10.2 8.9.1 8.8.2"
for stem in $stems; do
    stem_dash="$(echo "$stem" | sed 's/_/-/g')"
    echo
    echo '- [`'"$stem"'`](./PerformanceExperiments/'"$stem"'.v)'
    if [ "$(echo $coq_versions | wc -w)" -eq 1 ]; then extra_bar="|"; extra_bar_space=" |"; fi
    echo
    echo -n '  '
    echo $coq_versions | sed 's/ / | /g; s/$/'"$extra_bar_space"'/g'
    echo -n '  '
    echo $coq_versions | sed 's/[^ ]\+/--/g; s/ /|/g; s/$/'"$extra_bar"'/g'
    echo -n '  '
    echo $coq_versions | sed 's/ / | /g; s,\([^ |]\+\),<a href="https://coq-community.github.io/coq-performance-tests/\1/'"${stem_dash}"'.svg">"<img src="https://coq-community.github.io/coq-performance-tests/\1/'"${stem_dash}"'.svg" height=100px /></a>,g; s/$/'"$extra_bar_space"'/g'
done
