#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build
.lake/build/bin/article
pdflatex -interaction=nonstopmode -halt-on-error -output-directory _out _out/note.tex > _out/pdf-build.log
pdflatex -interaction=nonstopmode -halt-on-error -output-directory _out _out/note.tex >> _out/pdf-build.log
python3 check.py

cp _out/note.tex ../note.tex
cp _out/note.pdf ../note.pdf
python3 ../check_links.py
