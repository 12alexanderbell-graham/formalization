import sys, pathlib
root = sys.argv[1]
p = pathlib.Path(root) / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
a = "0.005225[src>fs_neg_wall_shear_window] (Asaithambi 2005), 0.005222[src>fs_neg_wall_shear_window] (Zhang–Chen 2009), 0.005226[src>fs_neg_wall_shear_window] (Salama 2004)"
b = "0.005226[src>fs_neg_wall_shear_window] (Asaithambi 2005), 0.005222[src>fs_neg_wall_shear_window] (Zhang–Chen 2009), 0.005225[src>fs_neg_wall_shear_window] (Salama 2004)"
assert t.count(a) == 1
p.write_text(t.replace(a, b), encoding="utf-8")
