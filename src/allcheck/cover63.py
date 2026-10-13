import sys, os, json, random, hashlib, argparse, tempfile, pathlib
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
import chess, chess.pgn
import enc, run

CASES = [(kw, kb, c) for c in (0, 1) for kw in range(64) for kb in range(64) if enc.cheb(kw, kb) > 1]
D = os.path.join(HERE, '..', '..', 'data')


def ok(r):
    return r['status'] == 'UNSAT_VERIFIED' and all(r['chk%d_exit' % i] == 0 for i in (1, 2, 3))


def cnf(i):
    kw, kb, c = CASES[i]
    return enc.build(kw, kb, bool(c), 64).dimacs()


def h(r):
    return hashlib.sha256(cnf(r['idx']).encode()).hexdigest() == r['cnf_sha256']


def resolve(r):
    d = pathlib.Path(tempfile.mkdtemp(prefix='cert_'))
    open(d / 'f.cnf', 'w').write(cnf(r['idx']))
    s = run.solve(d / 'f.cnf', d, 7200, True, [])
    return ok(s) and s['cnf_sha256'] == r['cnf_sha256']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sample', default='40')
    ap.add_argument('--resolve', default='0')
    ap.add_argument('--maxt', type=float, default=30)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--procs', type=int, default=os.cpu_count())
    a = ap.parse_args()
    R = [json.loads(l) for l in open(os.path.join(D, 'allcheck', 'cases.jsonl'))]
    sq = chess.square_name
    cov = [r['idx'] for r in R if ok(r) and (r['kw'], r['kb'], r['check']) == (sq(CASES[r['idx']][0]), sq(CASES[r['idx']][1]), CASES[r['idx']][2])]
    rnd = random.Random(a.seed)
    pick = lambda L, n: L if n == 'all' else rnd.sample(L, min(int(n), len(L)))
    with Pool(a.procs) as p:
        hs = p.map(h, pick(R, a.sample))
        rs = p.map(resolve, pick([r for r in R if a.resolve == 'all' or r['seconds'] < a.maxt], a.resolve)) if a.resolve != '0' else []
    print('cases: %d/%d UNSAT at >= 64 legal moves, all checks; %d proofs, %.1f GB, %.1f core-hours' % (
        len(set(cov)), len(CASES), len(R), sum(r['proof_bytes'] for r in R) / 1e9, sum(r['seconds'] for r in R) / 3600))
    print('CNF hashes re-derived: %d, mismatches %d' % (len(hs), hs.count(False)))
    print('re-solved with three LRAT checkers: %d, failed %d' % (len(rs), rs.count(False)))
    G = chess.pgn.read_game(open(os.path.join(D, 'allcheck63.pgn')))
    b = G.end().board()
    M = list(b.legal_moves)
    w = (not G.errors and G.board().fen() == chess.STARTING_FEN and b.fen() == G.headers['FinalFEN']
         and len(M) == 63 and all(b.gives_check(m) for m in M))
    print('reachable position with 63 legal moves, all checks: %s (%d plies)' % (w, b.ply()))
    good = sorted(set(cov)) == list(range(len(CASES))) and len(R) == len(CASES) and all(hs) and all(rs) and w
    print('max legal moves when every move is a check = 63: %s' % good)
    sys.exit(0 if good else 1)


if __name__ == '__main__':
    main()
