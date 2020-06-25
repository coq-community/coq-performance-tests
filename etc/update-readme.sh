#!/usr/bin/env bash

cd "$( dirname "${BASH_SOURCE[0]}" )"
cd ..

README="README.md"

line=$(grep -n -m 1 '^### PerformanceExperiments plots' "$README" | cut -f1 -d:)
head_part="$(head -n $line "$README")"
prerest_part="$(tail -n +$(($line+1)) "$README")"
line_rest="$( (echo "$prerest_part"; echo "EOF") | grep -n -m 1 -v '^$\|^- \|^  ' | cut -f1 -d:)"
rest_part="$(echo "$prerest_part" | tail -n +$line_rest)"
{
    echo "$head_part"
    PerformanceExperiments/gen-listing.sh "$@"
    if [ ! -z "$rest_part" ]; then echo; echo "$rest_part"; fi
} > "$README"
