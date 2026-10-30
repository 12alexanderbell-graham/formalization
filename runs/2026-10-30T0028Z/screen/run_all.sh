#!/bin/sh
# reference.py (slow, ~2 min) regenerates ref.pkl; the rest compare printed formulas against it.
cd "$(dirname "$0")"
[ -f ref.pkl ] || python3 reference.py > reference_out.txt
for f in cv2007.py cv2008_fits.py visser2004_eos.py chiba_nakamura1998.py vitagliano2010.py agl2012.py ccs2008.py cls2011.py dunsby_luongo2016.py; do
  echo "##### $f"; python3 $f
done
