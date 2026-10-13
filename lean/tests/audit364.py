import argparse, hashlib, os, random, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = Path(os.environ.get("AUDIT364", ROOT / ".lake" / "build" / "bin" / "audit364"))
TSV = ROOT / "data" / "records364.tsv"


def run(idx, tmp):
    out = subprocess.run([str(EXE), os.path.join(tmp, "r")] + [str(i) for i in idx],
                         capture_output=True, text=True, check=True).stdout.split("\n")
    res = []
    for l in out:
        if not l:
            continue
        i, wf = l.split()
        p = os.path.join(tmp, "r." + i)
        h = hashlib.sha256()
        with open(p, "rb") as f:
            for b in iter(lambda: f.read(1 << 20), b""):
                h.update(b)
        os.unlink(p)
        res.append((int(i), h.hexdigest(), wf == "true"))
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sample", type=int, default=30)
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--chunk", type=int, default=40)
    a = ap.parse_args()
    want = {int(r[0]): r[5] for r in (l.split() for l in open(TSV))}
    known = set()
    for f in (ROOT.parent / "data").rglob("*"):
        if f.is_file() and f.suffix != ".pgn":
            known |= set(re.findall(r"[0-9a-f]{64}", f.read_text(errors="ignore")))
    missing = [i for i, h in want.items() if h not in known]
    print(f"table hashes found in the certificate data: {len(want) - len(missing)}/{len(want)}")
    n = int(subprocess.run([str(EXE), "count"], capture_output=True, text=True, check=True).stdout)
    print(f"records: {n} lean, {len(want)} table")
    if a.all:
        idx = list(range(len(want)))
    else:
        idx = sorted({0, 1805, 1806, 3604, 3605, len(want) - 1} | set(random.Random(a.seed).sample(range(len(want)), a.sample)))
    chunks = [idx[k:k + a.chunk] for k in range(0, len(idx), a.chunk)]
    with tempfile.TemporaryDirectory() as tmp:
        with ThreadPoolExecutor(a.jobs) as ex:
            res = [x for r in ex.map(lambda c: run(c, tmp), chunks) for x in r]
    bad = [i for i, h, _ in res if h != want[i]]
    nwf = [i for i, _, wf in res if not wf]
    print(f"checked {len(res)} records, sha256 mismatches {len(bad)}, not well-formed {len(nwf)}")
    if bad or nwf:
        print("first bad:", bad[:20], nwf[:20])
    sys.exit(1 if missing or bad or nwf or n != len(want) or len(res) != len(idx) else 0)


if __name__ == "__main__":
    main()
