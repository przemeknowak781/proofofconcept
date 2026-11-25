"""Check release bytes, then optionally repeat the published and independent calculations."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import zipfile

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--numbers", action="store_true", help="repeat the numerical checks")
parser.add_argument("--bin", type=Path, help="also enumerate with geng, multig and count_trees from this directory")
args = parser.parse_args()
tree = json.loads((root / "github-tree-24523144.json").read_bytes())
if tree["truncated"] or tree["sha"] != "b4c5b60f61766ea11cb7e72cc493181ac06f6c68":
    sys.exit("unexpected upstream tree")
blobs = {item["path"]: item["sha"] for item in tree["tree"] if item["type"] == "blob"}
release = root / "vendor/spanning-trees-per-edge-v2.0.0.zip"
if hashlib.md5(release.read_bytes()).hexdigest() != "de22a0b8b1c09c8b53029629b43f39df":
    sys.exit("release MD5 mismatch")
with zipfile.ZipFile(release) as archive:
    files = [f for f in archive.infolist() if not f.is_dir()]
    if len(files) != 76 or len({f.filename for f in files}) != 76:
        sys.exit("unexpected release inventory")
    for item in files:
        data = archive.read(item)
        sha = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        if blobs.get(item.filename) != sha or (root / item.filename).read_bytes() != data:
            sys.exit(f"release mismatch: {item.filename}")
print("OK: 76 release files match Zenodo and the Git tree.", flush=True)


def execute(script, *arguments):
    return subprocess.run([sys.executable, "-E", "-B", "-X", "utf8", str(script), *arguments],
                          cwd=script.parent, check=True, stdout=subprocess.PIPE, encoding="utf8").stdout.splitlines()


if args.numbers or args.bin:
    folder = root / "spanning-trees-per-edge/verify"
    for stem, params in [("certify_intervals", []), ("check_class", ["3", "300"])]:
        if execute(folder / (stem + ".py"), *params) != (folder / (stem + ".out")).read_text(encoding="utf8").splitlines():
            sys.exit(f"reference output mismatch: {stem}")
        print("OK:", stem, flush=True)
    params = [str(args.bin.resolve())] if args.bin else []
    rows = execute(root / "audyt/reproduce.py", *params)
    if rows[-1] != "Total: 8350006":
        sys.exit("unexpected total")
    if args.bin:
        expected = (root / "audyt/exact-results.txt").read_text(encoding="utf8").splitlines()
        if rows[-len(expected):] != expected:
            sys.exit("independent enumeration mismatch")
    print("\n".join(rows))
