#! /bin/sh

MARKDOWNIZE=../../../markdownize/markdownize.py

echo "* Markdownizing inductive_sets.clj *"
python3 $MARKDOWNIZE -i ./inductive_sets.clj -o ./inductive_sets.clj.md -l clojure -b ";;{" -e ";;}" -rp ";; "
echo " ==> done"

echo "* Pandocize inductive_sets.clj.mk *"
pandoc -s ./inductive_sets.clj.md -o inductive_sets.clj.pdf --latex-engine=xelatex  --toc --highlight-style=tango
echo " ==> done"

