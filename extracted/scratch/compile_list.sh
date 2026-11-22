#!/bin/zsh
# compile the files listed in $1 sequentially
cd "$(dirname "$0")/.."
while read f; do ./scratch/compile_one.sh "scratch/src/$f"; done < "$1"
echo "DONE $1" >> scratch/compile_summary.txt
