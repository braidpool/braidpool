#!/bin/bash

DIR='./figures'
for figure in $DIR/*.dot;
do
    outfile=`basename -s .dot $figure`
    dot $figure -Tpdf -o $DIR/$outfile.pdf
done
