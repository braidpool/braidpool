#!/bin/bash

DIR='./figures'
for figure in $DIR/*.dot;
do
    outfile=`basename -s .dot $figure`
    dot $figure -Tpdf -o $DIR/$outfile.pdf
    dot $figure -Tpng -o $DIR/$outfile.png
done
