#!/bin/bash

# Clean up generated LaTeX compilation files
# Preserves: .pdf, .tex, .png, .gitignore

echo "Cleaning up generated LaTeX files..."

rm -f *.aux
rm -f *.fdb_latexmk
rm -f *.fls
rm -f *.log
rm -f *.out
rm -f *.synctex.gz

echo "Done! Kept all .pdf, .tex, .png files and .gitignore"
