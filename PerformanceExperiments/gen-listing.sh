#!/usr/bin/env bash

# Pass this script a list of file names, and it'll print the relevant
# lines for README.md to display things

# https://stackoverflow.com/a/246128/377022
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

stems="$@"
stems="$(echo "$stems" | tr ' ' '\n' | sed 's/\.v$//g' | tr '\n' ' ')"
extra_bar=""
extra_bar_space=""
coq_versions="$(grep -o 'COQ_VERSION:.*$' .github/workflows/coq.yml | sed 's/COQ_VERSION://g; s/\[//g; s/\]//g; s/[ "'"'"']//g; s/,/ /g')"
for stem in $stems; do
    stem_dash="$(echo "$stem" | sed 's,[_/],-,g')"
    echo
    echo '- [`'"$stem"'`](./PerformanceExperiments/'"$stem"'.v)'
    if [ "$(echo $coq_versions | wc -w)" -eq 1 ]; then extra_bar="|"; extra_bar_space=" |"; fi
    echo
    echo -n '  '
    echo $coq_versions | sed 's/-native//g; s/ / | /g; s/$/'"$extra_bar_space"'/g'
    echo -n '  '
    echo $coq_versions | sed 's/-native//g; s/[^ ]\+/--/g; s/ /|/g; s/$/'"$extra_bar"'/g'
    echo -n '  '
    echo $coq_versions | sed 's/ / | /g; s,\([^ |]\+\),<a href="https://coq-community.github.io/coq-performance-tests/\1/'"${stem_dash}"'.svg"><img src="https://coq-community.github.io/coq-performance-tests/\1/'"${stem_dash}"'.svg" height=100px /></a>,g; s/$/'"$extra_bar_space"'/g'
done
