#!/usr/bin/env bash
set -euo pipefail

# Usage: ./convert_dot.sh [directory]
DIR="${1:-.}"

shopt -s nullglob

for f in "$DIR"/*.dot; do
    base="$(basename "$f" .dot)"
    out="$DIR/$base.png"
    echo "Converting: $f -> $out"
    dot -Tpng "$f" -o "$out"
done

echo "Done."
