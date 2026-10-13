import hashlib
import os
import random
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = Path(os.environ.get("ENC63", ROOT / ".lake" / "build" / "bin" / "enc63"))
CASES = ROOT.parent / "data" / "allcheck" / "cases.jsonl"


def lean_hash(i: int) -> str:
    out = subprocess.run([str(EXE), "case", str(i)], capture_output=True, check=True).stdout
    return hashlib.sha256(out).hexdigest()


def main() -> None:
    recs = [json.loads(l) for l in open(CASES)]
    listing = subprocess.run([str(EXE), "cases"], capture_output=True, text=True, check=True).stdout.split("\n")
    listing = [l.split() for l in listing if l]
    order_bad = sum(
        1 for r, l in zip(recs, listing) if [str(r["idx"]), r["kw"], r["kb"], str(r["check"])] != l
    )
    print(f"case list: {len(listing)} lean, {len(recs)} records, order mismatches {order_bad + abs(len(listing) - len(recs))}")
    sel = sys.argv[1] if len(sys.argv) > 1 else "all"
    idx = list(range(len(recs))) if sel == "all" else sorted(random.Random(0).sample(range(len(recs)), int(sel)))
    jobs = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    with ThreadPoolExecutor(jobs) as ex:
        hs = list(ex.map(lean_hash, idx))
    bad = [i for i, h in zip(idx, hs) if h != recs[i]["cnf_sha256"]]
    print(f"cnf sha256 compared: {len(idx)}, mismatches {len(bad)}")
    if bad:
        print("first mismatches:", bad[:20])
    sys.exit(1 if bad or order_bad else 0)


if __name__ == "__main__":
    main()
