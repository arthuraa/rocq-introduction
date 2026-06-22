#!/bin/bash

if [ "$#" -ne 2 ]; then
    echo "usage: $0 OUT_DIR LINES_TO_SKIP" >&2
    exit 1
fi

out_dir=$1
skip=$2

# Usage: generate <input file> <output directory> <skip count>
# Example: generate theories/foo.v public 1
# generates the exercise version of the file at public/theories/foo.v
function generate {
    IN=$1
    OUT=$2
    COUNT=$3

    skip_replacement="\"\n\" x ${COUNT}"
    admitted_replacement="\"Proof. Admitted.\" . ${skip_replacement}"

    leave_exercise_only_regex="s/\(\*[[:blank:]]*<exercise-only>(?:[[:space:]]*)((?:\n|.)*?)[[:space:]]*<\/exercise-only>[[:blank:]]*\*\)/\$1/g"
    leave_exercise_inv_only_regex="s/\(\*[[:blank:]]*<exercise-inv-only>[[:blank:]]*\*\)(?:[[:space:]]*)((?:\n|.)*?)[[:space:]]*\(\*[[:blank:]]*<\/exercise-inv-only>[[:blank:]]*\*\)/\$1/g"
    remove_solution_regex="s/\(\*[[:blank:]]*<solution>[[:blank:]]*\*\)(?:[[:space:]]*)((?:\n|.)*?)[[:space:]]*\(\*[[:blank:]]*<\/solution>[[:blank:]]*\*\)/${skip_replacement}/ge"
    remove_solution_inv_only_regex="s/\(\*[[:blank:]]*<solution-inv-only>(?:[[:space:]]*)((?:\n|.)*?)[[:space:]]*<\/solution-inv-only>[[:blank:]]*\*\)//g"
    skip_regex="s/\(\*[[:blank:]]*<skip \/>[[:blank:]]*\*\)/${skip_replacement}/ge"

    admitted_regex="s/(.*)\(\*[[:blank:]]*<admitted>[[:blank:]]*\*\)(?:[[:space:]]*)((?:\n|.)*?)[[:space:]]*\(\*[[:blank:]]*<\/admitted>[[:blank:]]*\*\)/${admitted_replacement}/ge"

    full_regex="$remove_solution_regex;$remove_solution_inv_only_regex;$leave_exercise_only_regex;$leave_exercise_inv_only_regex;$skip_regex;$admitted_regex"

    cat "$IN" | perl -0777 -pe "$full_regex" > $OUT

}

for file in src/*.v; do
    base=$(basename $file)
    generate $file "${out_dir}/${base}" $skip
done

mkdir -p $out_dir

cp src/_CoqProject src/*Makefile* $out_dir
