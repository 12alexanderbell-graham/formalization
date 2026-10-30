# usage: python3 crop.py page y0 y1 name   (y in pixels at 200 dpi, page 1700x2200)
import sys
from PIL import Image
p, y0, y1, name = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
im = Image.open(f'/tmp/screen2_1628/pg{p}-{p}.png').convert('L')
c = im.crop((100, y0, 1650, y1)).convert('P', palette=Image.ADAPTIVE, colors=16)
out = f'/home/claude/formalization/runs/2026-10-30T1628Z/screen2/{name}.png'
c.save(out, optimize=True)
import os; print(out, os.path.getsize(out))
