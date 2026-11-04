# F01, F02, F04, F06 applied together (independent edits; errors are attributed per constant/file)
import subprocess, sys
from pathlib import Path
here = Path(__file__).resolve().parent.parent / "redteamF"
for n in ["d01", "d02", "d04", "d06"]:
    subprocess.run([sys.executable, str(here / n / "apply.py"), sys.argv[1]], check=True)
