import sys, hashlib, argparse

W, BL = 'PNBRQ', 'pnbrq'
SYM = W + BL
ORTH = [(1, 0), (-1, 0), (0, 1), (0, -1)]
DIAG = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
KN = [(1, 2), (2, 1), (-1, 2), (-2, 1), (1, -2), (2, -1), (-1, -2), (-2, -1)]
E1, F1, G1, H1, D1, C1, B1, A1 = 4, 5, 6, 7, 3, 2, 1, 0


def fr(s):
    return s & 7, s >> 3


def sq(f, r):
    return f + 8 * r if 0 <= f < 8 and 0 <= r < 8 else None


def ray(s, d):
    f, r = fr(s)
    out = []
    while True:
        f, r = f + d[0], r + d[1]
        x = sq(f, r)
        if x is None:
            return out
        out.append(x)


def direction(a, b):
    fa, ra = fr(a)
    fb, rb = fr(b)
    df, dr = fb - fa, rb - ra
    if (df == 0) == (dr == 0) and abs(df) != abs(dr):
        return None
    if df == 0 and dr == 0:
        return None
    return ((df > 0) - (df < 0), (dr > 0) - (dr < 0))


def between(a, b):
    d = direction(a, b)
    if d is None:
        return []
    out = []
    for x in ray(a, d):
        if x == b:
            return out
        out.append(x)
    return []


def cheb(a, b):
    fa, ra = fr(a)
    fb, rb = fr(b)
    return max(abs(fa - fb), abs(ra - rb))


def knight(s):
    f, r = fr(s)
    return [x for x in (sq(f + a, r + b) for a, b in KN) if x is not None]


class Enc:
    def __init__(s, kw, kb, check):
        s.kw, s.kb, s.check = kw, kb, check
        s.nv, s.cls, s.cache = 0, [], {}
        s.x = {}
        for q in range(64):
            if q in (kw, kb):
                continue
            s.x[q] = {k: s.var() for k in SYM}
            s.x[q]['.'] = s.var()
        for q in s.x:
            L = list(s.x[q].values())
            s.cls.append(L)
            for i in range(len(L)):
                for j in range(i + 1, len(L)):
                    s.cls.append([-L[i], -L[j]])
            if fr(q)[1] in (0, 7):
                s.cls.append([-s.x[q]['P']])
                s.cls.append([-s.x[q]['p']])

    def var(s):
        s.nv += 1
        return s.nv

    def p(s, q, k):
        if q == s.kw or q == s.kb:
            return False
        return s.x[q][k]

    def empty(s, q):
        return s.p(q, '.')

    def gate(s, op, L):
        if op == 'and':
            if any(l is False for l in L):
                return False
            L = sorted(set(l for l in L if l is not True))
            if not L:
                return True
        else:
            if any(l is True for l in L):
                return True
            L = sorted(set(l for l in L if l is not False))
            if not L:
                return False
        if len(L) == 1:
            return L[0]
        if any(-l in L for l in L):
            return op == 'or'
        key = (op, tuple(L))
        if key in s.cache:
            return s.cache[key]
        g = s.var()
        if op == 'and':
            for l in L:
                s.cls.append([-g, l])
            s.cls.append([g] + [-l for l in L])
        else:
            for l in L:
                s.cls.append([g, -l])
            s.cls.append([-g] + L)
        s.cache[key] = g
        return g

    def AND(s, L):
        return s.gate('and', list(L))

    def OR(s, L):
        return s.gate('or', list(L))

    def NOT(s, l):
        return (not l) if isinstance(l, bool) else -l

    def has(s, q, syms):
        return s.OR([s.p(q, k) for k in syms])

    def wocc(s, q):
        return True if q == s.kw else s.has(q, W)

    def bocc(s, q):
        return True if q == s.kb else s.has(q, BL)

    def clear(s, a, b, emp=(), occ=()):
        L = []
        for q in between(a, b):
            if q in emp:
                continue
            if q in occ:
                return False
            L.append(s.empty(q))
        return s.AND(L)

    def attacked(s, K, white, kpos, emp=(), occ=(), excl=()):
        bad = set(emp) | set(occ) | set(excl)
        T = []
        for d in ORTH + DIAG:
            syms = ('RQ' if d in ORTH else 'BQ')
            syms = syms if white else syms.lower()
            for q in ray(K, d):
                if q not in bad:
                    T.append(s.AND([s.has(q, syms), s.clear(K, q, emp, occ)]))
        for q in knight(K):
            if q not in bad:
                T.append(s.p(q, 'N' if white else 'n'))
        f, r = fr(K)
        for df in (-1, 1):
            q = sq(f + df, r - 1 if white else r + 1)
            if q is not None and q not in bad:
                T.append(s.p(q, 'P' if white else 'p'))
        k = kpos[0] if white else kpos[1]
        if k is not None and cheb(k, K) == 1:
            T.append(True)
        return s.OR(T)

    def attB(s, K, emp=(), occ=(), excl=(), kw=None):
        return s.attacked(K, False, (kw, s.kb), emp, occ, excl)

    def attW(s, K, emp=(), occ=(), excl=(), kw=None):
        return s.attacked(K, True, (kw if kw is not None else s.kw, s.kb), emp, occ, excl)

    def direct(s, t, T, emp, occ=()):
        K = s.kb
        if T == 'N':
            return cheb(t, K) <= 2 and K in knight(t)
        if T == 'P':
            ft, rt = fr(t)
            fk, rk = fr(K)
            return rk == rt + 1 and abs(fk - ft) == 1
        d = direction(t, K)
        if d is None or (T == 'R' and d not in ORTH) or (T == 'B' and d not in DIAG):
            return False
        return s.clear(t, K, emp, occ)

    def require(s, l):
        if l is False:
            s.cls.append([])
        elif l is not True:
            s.cls.append([l])

    def build(s, thr, allcheck=True):
        kw, kb = s.kw, s.kb
        s.require(s.NOT(s.attW(kb)))
        a = s.attB(kw, kw=kw)
        s.require(a if s.check else s.NOT(a))
        s.ep = {}
        for f in range(8):
            q5, q6, q7 = sq(f, 4), sq(f, 5), sq(f, 6)
            if kb in (q5, q6, q7) or kw in (q5, q6, q7):
                continue
            v = s.var()
            s.ep[f] = v
            s.cls += [[-v, s.x[q5]['p']], [-v, s.x[q6]['.']], [-v, s.x[q7]['.']]]
        E = list(s.ep.values())
        for i in range(len(E)):
            for j in range(i + 1, len(E)):
                s.cls.append([-E[i], -E[j]])
        s.cr = {}
        if kw == E1 and not s.check:
            for name, rq in (('K', H1), ('Q', A1)):
                if rq != kb:
                    v = s.var()
                    s.cr[name] = v
                    s.cls.append([-v, s.x[rq]['R']])
        for col in (W, BL):
            s.material(col)
        s.moves = []
        for q in s.x:
            for T in 'NBRQ':
                for t in s.targets(q, T):
                    s.add_move(q, t, None, T, s.AND([s.p(q, T), s.NOT(s.wocc(t))]) if T == 'N' else
                               s.AND([s.p(q, T), s.clear(q, t), s.NOT(s.wocc(t))]))
            f, r = fr(q)
            if r in (0, 7):
                continue
            t = sq(f, r + 1)
            if t not in (kw, kb):
                s.add_pawn(q, t, s.AND([s.p(q, 'P'), s.empty(t)]))
                if r == 1 and sq(f, 3) not in (kw, kb):
                    s.add_pawn(q, sq(f, 3), s.AND([s.p(q, 'P'), s.empty(t), s.empty(sq(f, 3))]))
            for df in (-1, 1):
                t = sq(f + df, r + 1)
                if t is None or t in (kw, kb):
                    continue
                s.add_pawn(q, t, s.AND([s.p(q, 'P'), s.has(t, BL)]))
                if r == 4 and (f + df) in s.ep:
                    s.add_move(q, t, None, 'P', s.AND([s.p(q, 'P'), s.ep[f + df]]), ep=sq(f + df, 4))
        for t in range(64):
            if cheb(kw, t) == 1 and cheb(kb, t) > 1:
                pseudo = s.NOT(s.wocc(t))
                legal = s.AND([pseudo, s.NOT(s.attB(t, emp=(kw,), excl=(t,), kw=t))])
                chk = s.attW(kb, emp=(kw,), occ=(t,), excl=(t,), kw=t)
                s.moves.append(((kw, t, None), 'K', legal, chk, 1))
        if 'K' in s.cr:
            legal = s.AND([s.cr['K'], s.empty(F1), s.empty(G1), s.NOT(s.attB(E1, emp=(E1,))), s.NOT(s.attB(F1, emp=(E1,))),
                           s.NOT(s.attB(G1, emp=(E1, H1), occ=(F1,), kw=G1))])
            chk = s.OR([s.direct(F1, 'R', (E1, H1), (G1,)),
                        s.attW(kb, emp=(E1, H1), occ=(F1, G1), excl=(F1, G1), kw=G1)])
            s.moves.append(((E1, G1, None), 'K', legal, chk, 1))
        if 'Q' in s.cr:
            legal = s.AND([s.cr['Q'], s.empty(B1), s.empty(C1), s.empty(D1), s.NOT(s.attB(E1, emp=(E1,))),
                           s.NOT(s.attB(D1, emp=(E1,))), s.NOT(s.attB(C1, emp=(E1, A1), occ=(D1,), kw=C1))])
            chk = s.OR([s.direct(D1, 'R', (E1, A1), (C1,)),
                        s.attW(kb, emp=(E1, A1), occ=(D1, C1), excl=(D1, C1), kw=C1)])
            s.moves.append(((E1, C1, None), 'K', legal, chk, 1))
        cnt = []
        for key, T, legal, chk, w in s.moves:
            if legal is False:
                continue
            if allcheck and chk is not True:
                s.cls.append([s.NOT(legal)] + ([] if chk is False else [chk]))
            cnt += [legal] * w
        s.atleast(cnt, thr)
        return s

    def targets(s, q, T):
        out = []
        if T == 'N':
            out = knight(q)
        else:
            for d in (ORTH if T == 'R' else DIAG if T == 'B' else ORTH + DIAG):
                out += ray(q, d)
        return [t for t in out if t not in (s.kw, s.kb)]

    def add_pawn(s, q, t, pseudo):
        if fr(t)[1] == 7:
            for i, T in enumerate('NBRQ'):
                s.add_move(q, t, T, 'P', pseudo, w=4 if i == 0 else 0)
        else:
            s.add_move(q, t, None, 'P', pseudo)

    def add_move(s, q, t, pr, T, pseudo, ep=None, w=1):
        if pseudo is False:
            return
        emp = (q,) if ep is None else (q, ep)
        legal = s.AND([pseudo, s.NOT(s.attB(s.kw, emp=emp, occ=(t,), excl=(t,), kw=s.kw))])
        Tp = pr if pr else T
        chk = s.OR([s.direct(t, Tp, emp), s.attW(s.kb, emp=emp, occ=(t,), excl=(t,))])
        s.moves.append(((q, t, pr), T, legal, chk, w))

    def counter(s, L, k):
        prev = [True] + [False] * k
        for l in L:
            cur = [True] + [s.OR([prev[j], s.AND([l, prev[j - 1]])]) for j in range(1, k + 1)]
            prev = cur
        return prev

    def atleast(s, L, k):
        c = s.counter(L, k)
        if c[k] is False:
            s.cls.append([])
        elif c[k] is not True:
            s.cls.append([c[k]])

    def atmost(s, L, k):
        c = s.counter(L, k + 1)
        if c[k + 1] is True:
            s.cls.append([])
        elif c[k + 1] is not False:
            s.cls.append([-c[k + 1]])

    def material(s, col):
        P, N, B, R, Q = col
        sq_ = list(s.x)
        men = [s.x[q][k] for q in sq_ for k in col]
        s.atmost(men, 15)
        pawns = [s.x[q][P] for q in sq_]
        ex = []
        for k, base in ((N, 2), (R, 2), (Q, 1)):
            c = s.counter([s.x[q][k] for q in sq_], 15)
            ex += c[base + 1:]
        for colour in (0, 1):
            c = s.counter([s.x[q][B] for q in sq_ if (fr(q)[0] + fr(q)[1]) % 2 == colour], 15)
            ex += c[2:]
        s.atmost(pawns + ex, 8)

    def dimacs(s):
        cl = [c for c in s.cls if c is not None]
        out = ['p cnf %d %d\n' % (s.nv, len(cl))]
        out += [' '.join(map(str, c)) + ' 0\n' for c in cl]
        return ''.join(out)


def build(kw, kb, check, thr, allcheck=True):
    return Enc(kw, kb, check).build(thr, allcheck)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('kw'); ap.add_argument('kb')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('-t', type=int, default=64)
    ap.add_argument('-o', default='-')
    a = ap.parse_args()
    q = lambda n: 'abcdefgh'.index(n[0]) + 8 * (int(n[1]) - 1)
    d = build(q(a.kw), q(a.kb), a.check, a.t).dimacs()
    (sys.stdout if a.o == '-' else open(a.o, 'w')).write(d)
    sys.stderr.write(hashlib.sha256(d.encode()).hexdigest() + '\n')
