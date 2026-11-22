#!/bin/zsh
# compile one scratch file against the pinned Mathlib; log time and peak RSS
source ~/.elan/env
f=$1
cd "$(dirname "$0")/.."
out="scratch/log_$(basename "$f" .lean).txt"
start=$(date +%s)
/usr/bin/time -l lake env lean "$f" > "$out" 2>&1
rc=$?
end=$(date +%s)
peak=$(grep -i "maximum resident" "$out" | awk "{print \$1}")
echo "$(basename $f) rc=$rc time=$((end-start))s peakRSS=$(( peak / 1073741824 ))GB errors=$(grep -c 'error' "$out")" >> scratch/compile_summary.txt
