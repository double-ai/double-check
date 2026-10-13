import sys, os, json, glob, random, hashlib, argparse, tempfile, pathlib
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import benc, hard, run

E0, E1 = ['-n', '20', '--cap', '0'], ['-n', '22', '--cap', '1']
REPS = [(w, b) for w in range(64) for b in range(64)
        if max(abs(w % 8 - b % 8), abs(w // 8 - b // 8)) > 1 and (w, b) <= (w ^ 7, b ^ 7)]
IDX = {(benc.sqn(w), benc.sqn(b)): i for i, (w, b) in enumerate(REPS)}


def ok(r):
    return (r is not None and r.get('status') == 'UNSAT_VERIFIED'
            and all(r.get('chk%d_exit' % i) == 0 for i in (1, 2, 3)))


def build(kw, kb, enc):
    return benc.build_from_args(benc.parse_args(['--kw', kw, '--kb', kb] + enc + ['-o', '/dev/null']))


class H:
    def __init__(s, e):
        s.e, s.c = e, {}
        s.body = ''.join(' '.join(map(str, c)) + ' 0\n' for c in e.cls).encode()

    def sha(s, extra):
        k = len(extra)
        if k not in s.c:
            s.c[k] = hashlib.sha256(('p cnf %d %d\n' % (s.e.nv, len(s.e.cls) + k)).encode())
            s.c[k].update(s.body)
        h = s.c[k].copy()
        h.update(''.join(' '.join(map(str, c)) + ' 0\n' for c in extra).encode())
        return h.hexdigest()


def enc_n(enc):
    try:
        a = benc.parse_args(['--kw', 'a1', '--kb', 'c1'] + list(enc) + ['-o', '/dev/null'])
        d = benc.parse_args(['--kw', 'a1', '--kb', 'c1', '-n', str(a.n), '--cap', '1', '-o', '/dev/null'])
    except SystemExit:
        return None
    return a.n if vars(a) == vars(d) else None


def rows(f):
    R = {}
    for r in map(json.loads, open(f)):
        if R.get(r['idx']) is None or ok(r):
            R[r['idx']] = r
    return R


def row_hash(a):
    r, enc = a
    return H(build(r['kw'], r['kb'], enc)).sha([]) == r['cnf_sha256']


def resolve(a):
    kw, kb, enc, extra, sha = a
    e = build(kw, kb, enc)
    d = pathlib.Path(tempfile.mkdtemp(prefix='cert_'))
    hard.write_cnf(d / 'f.cnf', e.nv, e.cls, extra)
    s = run.solve(d / 'f.cnf', d, 7200, True, [])
    return ok(s) and s['cnf_sha256'] == sha


def tree(path):
    T = json.load(open(path))
    k = enc_n(T['enc_args'])
    if k is None or k > 23 or (T['kw'], T['kb']) not in IDX:
        return path, None, 'bad header', []
    e = build(T['kw'], T['kb'], T['enc_args'])
    h = H(e)
    if hashlib.sha256(h.body).hexdigest() != T['base_sha256']:
        return path, None, 'base sha', []
    N, F = T['nodes'], []

    def ver(i):
        nd = N[i]
        if nd['status'] == 'UNSAT_VERIFIED':
            x = [[u] for u in nd['units']]
            F.append((T['kw'], T['kb'], T['enc_args'], x, nd['rec']['cnf_sha256'], nd['rec']['seconds']))
            return ok(nd.get('rec')) and h.sha(x) == nd['rec']['cnf_sha256']
        sp = nd.get('split')
        if not sp:
            return False
        if sp['spec'] == 'caps':
            if nd['units']:
                return False
            want = [u for u, _ in hard.caps_cubes(e)]
        elif sp['spec'].startswith('chk:'):
            want = [nd['units'] + c for c in hard.chk_cubes(e, int(sp['spec'][4:]))]
        else:
            return False
        got = [N[c]['units'] for c in sp['children']]
        cr = sp.get('cover_rec')
        x = [[u] for u in nd['units']] + [[-l for l in u] for u in got]
        F.append((T['kw'], T['kb'], T['enc_args'], x, cr['cnf_sha256'], cr['seconds']))
        return (got == want and sp.get('cover') == 'UNSAT_VERIFIED' and ok(cr) and h.sha(x) == cr['cnf_sha256']
                and all(ver(c) for c in sp['children']))
    v = ver('r')
    return path, (IDX[(T['kw'], T['kb'])], k), ('VERIFIED %d' % len(F)) if v else 'FAIL', F


def witness():
    import chess.pgn
    G = chess.pgn.read_game(open(os.path.join(HERE, '..', 'data', 'witness22.pgn')))
    b, c = G.board(), 0
    for m in G.mainline_moves():
        assert m in b.legal_moves and b.gives_check(m) and b.piece_type_at(m.from_square) != chess.KING
        c += b.is_capture(m)
        b.push(m)
    return b.ply() == 22 and c == 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sample', default='40')
    ap.add_argument('--resolve', default='0')
    ap.add_argument('--maxt', type=float, default=30)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--procs', type=int, default=os.cpu_count())
    a = ap.parse_args()
    D = os.path.join(HERE, '..', 'data')
    b0, b1 = rows(os.path.join(D, 'b0.jsonl')), rows(os.path.join(D, 'b1.jsonl'))
    for R in (b0, b1):
        for i, r in R.items():
            assert (r['kw'], r['kb']) == (benc.sqn(REPS[i][0]), benc.sqn(REPS[i][1])), r
    G0 = sorted(i for i, r in b0.items() if ok(r))
    G1 = sorted(i for i, r in b1.items() if ok(r))
    rnd = random.Random(a.seed)
    pick = lambda L, n: L if n == 'all' else rnd.sample(L, min(int(n), len(L)))
    with Pool(a.procs) as p:
        hs = p.map(row_hash, [(b0[i], E0) for i in pick(G0, a.sample)] + [(b1[i], E1) for i in pick(G1, a.sample)])
        ts = p.map(tree, sorted(glob.glob(os.path.join(D, 'trees', '*.json'))))
        F = [(b0[i]['kw'], b0[i]['kb'], E0, [], b0[i]['cnf_sha256'], b0[i]['seconds']) for i in G0] + \
            [(b1[i]['kw'], b1[i]['kb'], E1, [], b1[i]['cnf_sha256'], b1[i]['seconds']) for i in G1]
        F = [f[:5] for f in F + [f for t in ts for f in t[3]] if a.resolve == 'all' or f[5] < a.maxt]
        rs = p.map(resolve, pick(F, a.resolve)) if a.resolve != '0' else []
    cov = set(G1) | {t[1][0] for t in ts if t[2].startswith('VERIFIED')}
    nf = sum(len(t[3]) for t in ts)
    good = all(hs) and all(rs) and all(t[2].startswith('VERIFIED') for t in ts)
    B0, B1 = len(G0) == 1806 and good, len(cov) == 1806 and good
    w = witness()
    print('B(0) <= 19: %s  (%d/1806 UNSAT at n=20, no capture)' % (B0, len(G0)))
    print('B(1) <= 22: %s  (%d direct UNSAT at n=22 + %d trees, %d tree formulas; %d uncovered)' % (B1, len(G1), len(ts), nf, 1806 - len(cov)))
    print('CNF hashes re-derived: %d rows + %d tree formulas, %d mismatches' % (len(hs), nf, hs.count(False) + sum(not t[2].startswith('VERIFIED') for t in ts)))
    print('re-solved with three LRAT checkers: %d, failed %d' % (len(rs), rs.count(False)))
    print('B(1) >= 22 witness replays: %s' % w)
    f = lambda C: 23 * (C // 2) + (19 if C % 2 == 0 else 22)
    N = max([f(C) for C in range(30)] + [f(x) + 1 + f(y) for x in range(30) for y in range(30 - x)])
    print('N <= %d' % N)
    sys.exit(0 if B0 and B1 and w and N == 364 else 1)


if __name__ == '__main__':
    main()
