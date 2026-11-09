import sys; sys.path.insert(0, __file__.rsplit("/d04/", 1)[0])
from common import edit
edit(sys.argv[1], [
 ("(negative convention, de Sitter has negative Ricci scalar; negative convention so de Sitter has minus twelve times Hubble rate squared)",
  "(negative convention, de Sitter has negative Ricci scalar; minus six times second derivative over (scale factor plus squared Hubble rate); negative convention so de Sitter has minus twelve times Hubble rate squared)"),
], "- Reworded the phrase of curv (added the blind formula clause).")
