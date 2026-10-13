import sys, os, json, time, pathlib, argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
import enc, run

CASES = [(kw, kb, c) for c in (0, 1) for kw in range(64) for kb in range(64) if enc.cheb(kw, kb) > 1]
SQ = lambda q: 'abcdefgh'[q & 7] + str((q >> 3) + 1)


def decode(e, model):
    import chess
    b = chess.Board(None)
    b.set_piece_at(e.kw, chess.Piece(chess.KING, chess.WHITE))
    b.set_piece_at(e.kb, chess.Piece(chess.KING, chess.BLACK))
    for q, d in e.x.items():
        for k, v in d.items():
            if k != '.' and v in model:
                b.set_piece_at(q, chess.Piece.from_symbol(k))
    cr = 0
    for name, v in e.cr.items():
        if v in model:
            cr |= chess.BB_H1 if name == 'K' else chess.BB_A1
    b.castling_rights = cr
    for f, v in e.ep.items():
        if v in model:
            b.ep_square = chess.square(f, 5)
    b.turn = chess.WHITE
    ms = list(b.legal_moves)
    return dict(fen=b.fen(), legal=len(ms), allcheck=all(b.gives_check(m) for m in ms), valid=b.is_valid() or b.status() == chess.STATUS_VALID)


def one(i, thr, tmo, work):
    kw, kb, c = CASES[i]
    d = pathlib.Path(work) / ('c%04d' % i)
    d.mkdir(parents=True, exist_ok=True)
    e = enc.build(kw, kb, bool(c), thr)
    open(d / 'f.cnf', 'w').write(e.dimacs())
    rec = run.solve(d / 'f.cnf', d, tmo, True, [])
    r = dict(idx=i, kw=SQ(kw), kb=SQ(kb), check=c, thr=thr, status=rec['status'], seconds=round(rec['seconds'], 2),
             timeout=tmo, cnf_sha256=rec['cnf_sha256'], proof_sha256=rec.get('proof_sha256'), proof_bytes=rec.get('proof_bytes'),
             chk1_exit=rec.get('chk1_exit'), chk2_exit=rec.get('chk2_exit'), chk3_exit=rec.get('chk3_exit'))
    if rec['status'] == 'SAT':
        r['sat'] = decode(e, rec['model'])
    (d / 'f.cnf').unlink(missing_ok=True)
    for f in d.iterdir():
        f.unlink()
    d.rmdir()
    return r


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('work'); ap.add_argument('--thr', type=int, default=64)
    ap.add_argument('--timeout', type=int, default=3600); ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--shard', type=int, default=0); ap.add_argument('--nshard', type=int, default=1)
    ap.add_argument('--idx', type=int, nargs='*')
    a = ap.parse_args()
    W = pathlib.Path(a.work); W.mkdir(parents=True, exist_ok=True)
    man = W / ('m%03d.jsonl' % a.shard)
    done = set()
    if man.exists():
        for l in open(man):
            r = json.loads(l)
            if r['status'] in ('UNSAT_VERIFIED', 'SAT') or r['timeout'] >= a.timeout:
                done.add(r['idx'])
    todo = a.idx if a.idx else [i for i in range(a.shard, len(CASES), a.nshard) if i not in done]
    with ThreadPoolExecutor(a.jobs) as ex, open(man, 'a') as out:
        fs = [ex.submit(one, i, a.thr, a.timeout, W / 'tmp') for i in todo]
        for f in as_completed(fs):
            r = f.result()
            out.write(json.dumps(r) + '\n'); out.flush()
            if r['status'] != 'UNSAT_VERIFIED':
                print(json.dumps(r), flush=True)
