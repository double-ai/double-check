import argparse, json, sys, hashlib, itertools
from collections import defaultdict

TN = 'PNBRQ'
P, N, B, R, Q = range(5)
EMP = 10
ORTH = [(1, 0), (-1, 0), (0, 1), (0, -1)]
DIAG = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
KN = [(1, 2), (2, 1), (-1, 2), (-2, 1), (1, -2), (2, -1), (-1, -2), (-2, -1)]

def sqn(s):
    return 'abcdefgh'[s & 7] + str((s >> 3) + 1)

def psq(x):
    return 'abcdefgh'.index(x[0]) + 8 * (int(x[1]) - 1)

def Fl(s):
    return s & 7

def Rk(s):
    return s >> 3

def onb(f, r):
    return 0 <= f < 8 and 0 <= r < 8

def pdir(c):
    return 1 if c == 0 else -1

def between(a, b):
    df, dr = Fl(b) - Fl(a), Rk(b) - Rk(a)
    if df == 0 and dr == 0:
        return None
    if df != 0 and dr != 0 and abs(df) != abs(dr):
        return None
    sf, sr = (df > 0) - (df < 0), (dr > 0) - (dr < 0)
    out, f, r = [], Fl(a) + sf, Rk(a) + sr
    while (f, r) != (Fl(b), Rk(b)):
        out.append(f + 8 * r)
        f += sf
        r += sr
    return out

def pawn_attacks(c, s):
    out = []
    r = Rk(s) + pdir(c)
    for df in (-1, 1):
        f = Fl(s) + df
        if onb(f, r):
            out.append(f + 8 * r)
    return out

def attacks_geom(p, c, s, k):
    if p == P:
        return k in pawn_attacks(c, s)
    df, dr = abs(Fl(k) - Fl(s)), abs(Rk(k) - Rk(s))
    if p == N:
        return (df, dr) in ((1, 2), (2, 1))
    b = between(s, k)
    if b is None:
        return False
    orth = (df == 0 or dr == 0)
    if p == R:
        return orth
    if p == B:
        return not orth
    return True

class Enc:
    def __init__(self, kw, kb, n, first=0, capmode='atmost', cap=0, start='c0', ep=True, promo=True,
                 init_check=False, redundant=True, pin_fen=None, pin_moves=None, single_check=True,
                 material=None, lemma_run=None, pin_shift=0):
        assert max(abs(Fl(kw) - Fl(kb)), abs(Rk(kw) - Rk(kb))) > 1, 'kings adjacent or equal'
        self.K = [kw, kb]
        self.n, self.first = n, first
        self.capmode, self.cap = capmode, cap
        self.start, self.ep, self.promo = start, ep, promo
        self.init_check, self.redundant = init_check, redundant
        self.single_check = single_check
        self.NK = [s for s in range(64) if s not in self.K]
        self.nv = 0
        self.cls = []
        self.X = []
        self.FR, self.TO, self.MP, self.RT, self.CAP, self.PROMO = [], [], [], [], [], []
        self.EPS, self.EPR, self.A = [], [], []
        self.groups = defaultdict(int)
        self.build()
        if material:
            self.add_material(material)
        if lemma_run is not None:

            L = lemma_run + 1
            for t0 in range(0, self.n - L + 1):
                self.add([self.CAP[t] for t in range(t0, t0 + L)], 'lemma')
        if pin_fen is not None:
            self.pin_start(pin_fen)
        if pin_moves is not None:
            self.pin_line(pin_moves, pin_shift)

    def v(self):
        self.nv += 1
        return self.nv

    def add(self, c, grp='misc'):
        self.cls.append(list(c))
        self.groups[grp] += 1

    def amo(self, lits, grp):
        lits = list(lits)
        if len(lits) <= 8:
            for a, b in itertools.combinations(lits, 2):
                self.add([-a, -b], grp)
        else:
            s_prev = None
            for i, x in enumerate(lits):
                if i < len(lits) - 1:
                    s = self.v()
                    self.add([-x, s], grp)
                    if s_prev is not None:
                        self.add([-s_prev, s], grp)
                        self.add([-x, -s_prev], grp)
                    s_prev = s
                else:
                    self.add([-x, -s_prev], grp)

    def exactly_one(self, lits, grp):
        lits = list(lits)
        self.add(lits, grp)
        self.amo(lits, grp)

    def col(self, t):
        return (self.first + t) % 2

    def allowed(self, c, f, g):
        ts = set()
        df, dr = Fl(g) - Fl(f), Rk(g) - Rk(f)
        if (abs(df), abs(dr)) in ((1, 2), (2, 1)):
            ts.add(N)
        btw = between(f, g)
        if btw is not None and not any(s in self.K for s in btw):
            if df == 0 or dr == 0:
                ts |= {R, Q}
            else:
                ts |= {B, Q}
        d = pdir(c)
        if df == 0 and dr == d:
            ts.add(P)
        if df == 0 and dr == 2 * d and Rk(f) == (1 if c == 0 else 6) and (f + 8 * d) not in self.K:
            ts.add(P)
        if abs(df) == 1 and dr == d:
            ts.add(P)
        return ts

    def ray(self, x, d):
        k, other = self.K[x], self.K[1 - x]
        out, f, r = [], Fl(k) + d[0], Rk(k) + d[1]
        while onb(f, r):
            s = f + 8 * r
            if s == other:
                break
            out.append(s)
            f += d[0]
            r += d[1]
        return out

    def ray_squares(self, x):
        out = set()
        for d in ORTH + DIAG:
            out |= set(self.ray(x, d))
        return out

    def attack_candidates(self, x):
        y, k = 1 - x, self.K[x]
        out = self.ray_squares(x)
        for s in self.NK:
            if attacks_geom(N, y, s, k) or attacks_geom(P, y, s, k):
                out.add(s)
        return out

    def board_layer(self, t):
        L = {}
        for s in self.NK:
            xs = [self.v() for _ in range(11)]
            L[s] = xs
            self.exactly_one(xs, 'onehot')
        self.X.append(L)

    def attack_layer(self, t):
        X = self.X[t]
        AX = []
        for x in (0, 1):
            y, k = 1 - x, self.K[x]
            alts = defaultdict(list)
            for s in self.NK:
                if attacks_geom(N, y, s, k):
                    alts[s].append([X[s][5 * y + N]])
                if attacks_geom(P, y, s, k):
                    alts[s].append([X[s][5 * y + P]])
            for d in ORTH + DIAG:
                sl = R if d in ORTH else B
                ray = self.ray(x, d)
                clear = None
                for j, s in enumerate(ray):
                    if j == 1:
                        clear = X[ray[0]][EMP]
                    elif j >= 2:
                        c = self.v()
                        self.add([-c, clear], 'clear')
                        self.add([-c, X[ray[j - 1]][EMP]], 'clear')
                        self.add([c, -clear, -X[ray[j - 1]][EMP]], 'clear')
                        clear = c
                    for p in (Q, sl):
                        alts[s].append(([clear] if clear is not None else []) + [X[s][5 * y + p]])
            A = {}
            for s, conj_list in alts.items():
                a = self.v()
                A[s] = a
                disj = []
                for conj in conj_list:
                    self.add([-l for l in conj] + [a], 'attack')
                    if len(conj) == 1:
                        disj.append(conj[0])
                    else:
                        aux = self.v()
                        for l in conj:
                            self.add([-aux, l], 'attack')
                        self.add([-l for l in conj] + [aux], 'attack')
                        disj.append(aux)
                self.add([-a] + disj, 'attack')
            AX.append(A)
        self.A.append(AX)

    def ep_layer(self, t):
        c = self.col(t)
        E = {}
        if not self.ep:
            self.EPS.append(E)
            return
        trank = 5 if c == 0 else 2
        e = 1 - c
        for s in self.NK:
            if Rk(s) != trank:
                continue
            dsq = s - 8 * pdir(c)
            osq = s + 8 * pdir(c)
            if dsq in self.K or osq in self.K:
                continue
            v = self.v()
            E[s] = v
            if t == 0:
                self.add([-v, self.X[0][dsq][5 * e + P]], 'ep')
                self.add([-v, self.X[0][s][EMP]], 'ep')
                self.add([-v, self.X[0][osq][EMP]], 'ep')
            else:
                fr, to, mp = self.FR[t - 1], self.TO[t - 1], self.MP[t - 1]
                self.add([-v, fr[osq]], 'ep')
                self.add([-v, to[dsq]], 'ep')
                self.add([-v, mp[P]], 'ep')
                self.add([-fr[osq], -to[dsq], -mp[P], v], 'ep')
        if t == 0:
            self.amo(E.values(), 'ep')
        self.EPS.append(E)

    def ply(self, t):
        c, e = self.col(t), 1 - self.col(t)
        X0, X1 = self.X[t], self.X[t + 1]
        FR = {s: self.v() for s in self.NK}
        TO = {s: self.v() for s in self.NK}
        MP = [self.v() for _ in range(5)]
        RT = [self.v() for _ in range(5)]
        CAP, PROMO = self.v(), self.v()
        self.FR.append(FR); self.TO.append(TO); self.MP.append(MP); self.RT.append(RT)
        self.CAP.append(CAP); self.PROMO.append(PROMO)
        self.exactly_one(FR.values(), 'move1')
        self.exactly_one(TO.values(), 'move1')
        self.exactly_one(MP, 'move1')
        self.exactly_one(RT, 'move1')

        EPR = {}
        if self.ep:
            rrank = 4 if c == 0 else 3
            for r in self.NK:
                if Rk(r) != rrank:
                    continue
                g = r + 8 * pdir(c)
                if g not in self.EPS[t]:
                    continue
                srcs = [r + df for df in (-1, 1) if onb(Fl(r) + df, Rk(r)) and (r + df) in self.NK]
                if not srcs:
                    continue
                v = self.v()
                EPR[r] = v
                self.add([-v, TO[g]], 'ep')
                self.add([-v, MP[P]], 'ep')
                self.add([-v, X0[r][5 * e + P]], 'ep')
                self.add([-v, self.EPS[t][g]], 'ep')
                self.add([-v, X0[g][EMP]], 'ep')
                self.add([-v] + [FR[s] for s in srcs], 'ep')
                self.add([-v, X1[r][EMP]], 'ep')
        self.EPR.append(EPR)
        for s in self.NK:
            self.add([-FR[s], -TO[s]], 'move1')

            self.add([-FR[s]] + [X0[s][5 * c + p] for p in range(5)], 'source')
            for p in range(5):
                self.add([-FR[s], -MP[p], X0[s][5 * c + p]], 'source')
                self.add([-FR[s], -X0[s][5 * c + p], MP[p]], 'source')

            for p in range(5):
                self.add([-TO[s], -X0[s][5 * c + p]], 'dest')

        for f in self.NK:
            for g in self.NK:
                if f == g:
                    continue
                ts = self.allowed(c, f, g)
                if not ts:
                    self.add([-FR[f], -TO[g]], 'geom')
                    continue
                if len(ts) < 5:
                    self.add([-FR[f], -TO[g]] + [MP[p] for p in sorted(ts)], 'geom')
                btw = between(f, g)
                if btw:
                    for s in btw:
                        self.add([-FR[f], -TO[g], X0[s][EMP]], 'transit')
                if P in ts:
                    if Fl(f) == Fl(g):
                        self.add([-FR[f], -TO[g], -MP[P], X0[g][EMP]], 'pawn')
                    else:
                        r = g - 8 * pdir(c)
                        if r in EPR:
                            self.add([-FR[f], -TO[g], -MP[P], -X0[g][EMP], EPR[r]], 'pawn')
                        else:
                            self.add([-FR[f], -TO[g], -MP[P], -X0[g][EMP]], 'pawn')

        epl = list(EPR.values())
        for g in self.NK:
            self.add([-TO[g], X0[g][EMP], CAP], 'cap')
            self.add([-CAP, -TO[g], -X0[g][EMP]] + epl, 'cap')
        for v in epl:
            self.add([-v, CAP], 'cap')

        last = 7 if c == 0 else 0
        LT = [TO[g] for g in self.NK if Rk(g) == last]
        self.add([-PROMO, MP[P]], 'promo')
        self.add([-PROMO] + LT, 'promo')
        for l in LT:
            self.add([-MP[P], -l, PROMO], 'promo')
        for p in range(5):
            self.add([PROMO, -MP[p], RT[p]], 'promo')
            self.add([PROMO, -RT[p], MP[p]], 'promo')
        self.add([-PROMO, -RT[P]], 'promo')
        if not self.promo:
            self.add([-PROMO], 'promo')

        for s in self.NK:
            self.add([-FR[s], X1[s][EMP]], 'update')
            for p in range(5):
                self.add([-TO[s], -RT[p], X1[s][5 * c + p]], 'update')
            ch = self.v()
            lits = [FR[s], TO[s]] + ([EPR[s]] if s in EPR else [])
            self.add([-ch] + lits, 'frame')
            for l in lits:
                self.add([-l, ch], 'frame')
            for k in range(11):
                self.add([ch, -X0[s][k], X1[s][k]], 'frame')
                self.add([ch, X0[s][k], -X1[s][k]], 'frame')

    def build(self):
        n = self.n
        for t in range(n + 1):
            self.board_layer(t)

        for t in range(n + 1):
            self.attack_layer(t)
        self.ep_layer(0)
        for t in range(n):
            self.ply(t)
            self.ep_layer(t + 1)
        if self.start == 'c0':
            for s in self.NK:
                if Rk(s) in (0, 7):
                    self.add([-self.X[0][s][P]], 'start')
                    self.add([-self.X[0][s][5 + P]], 'start')
            for a in self.A[0][1 - self.first].values():
                self.add([-a], 'start')
        if n >= 1:

            self.amo(self.A[0][self.first].values(), 'check')
        if self.init_check:
            self.add(list(self.A[0][self.first].values()), 'start')
        for t in range(n):
            c, e = self.col(t), 1 - self.col(t)
            for a in self.A[t + 1][c].values():
                self.add([-a], 'legal')
            self.add(list(self.A[t + 1][e].values()), 'check')
            if self.single_check and t + 1 <= n - 1:
                self.amo(self.A[t + 1][e].values(), 'check')
        self.captures()
        if self.redundant:
            self.redundant_families()

    def captures(self):
        caps = self.CAP
        if self.capmode == 'any':
            return
        m = self.cap
        if self.capmode == 'none' or m == 0 and self.capmode == 'atmost':
            for c in caps:
                self.add([-c], 'capcount')
            return

        k = m + 1
        S = []
        for i, x in enumerate(caps):
            row = [self.v() for _ in range(k)]
            for j in range(k):
                prev_j = S[i - 1][j] if i > 0 else None
                prev_jm = (S[i - 1][j - 1] if i > 0 else None) if j > 0 else 'T'

                if prev_j is not None:
                    self.add([-prev_j, row[j]], 'capcount')
                if prev_jm == 'T':
                    self.add([-x, row[j]], 'capcount')
                elif prev_jm is not None:
                    self.add([-x, -prev_jm, row[j]], 'capcount')
                cl = [-row[j]]
                if prev_j is not None:
                    cl.append(prev_j)
                if prev_jm == 'T':
                    self.add(cl + [x], 'capcount')
                elif prev_jm is not None:
                    self.add(cl + [x], 'capcount')
                    self.add(cl + [prev_jm], 'capcount')
                else:
                    self.add(cl, 'capcount')
            S.append(row)
        last = S[-1]
        if self.capmode in ('atmost', 'exact'):
            self.add([-last[m]], 'capcount')
        if self.capmode == 'exact' and m >= 1:
            self.add([last[m - 1]], 'capcount')
        self.capS = S

    def redundant_families(self):
        n = self.n
        for t in range(n):
            c, e = self.col(t), 1 - self.col(t)
            FR, TO, EPR, RT = self.FR[t], self.TO[t], self.EPR[t], self.RT[t]
            ke = self.K[e]
            safe_before = (t >= 1) or (self.start == 'c0')
            raysq_e = self.ray_squares(e)
            disc = [FR[s] for s in self.NK if s in raysq_e] + [EPR[r] for r in EPR if r in raysq_e]
            if safe_before:

                for q, a in self.A[t + 1][e].items():
                    btw = between(q, ke) or []
                    cl = [-a, TO[q]] + [FR[s] for s in btw] + [EPR[s] for s in btw if s in EPR]
                    self.add(cl, 'R1')

                for g in self.NK:
                    for p in range(5):
                        if not attacks_geom(p, c, g, ke) or (between(g, ke) and any(s in self.K for s in between(g, ke))):
                            self.add([-TO[g], -RT[p]] + disc, 'R4')

            kc = self.K[c]
            for q, a in self.A[t][c].items():
                btw = between(q, kc) or []
                cl = [-a, TO[q]] + ([EPR[q]] if q in EPR else []) + [TO[s] for s in btw]
                self.add(cl, 'R2')

            if t >= 1 or self.init_check:
                cand = self.attack_candidates(c)
                for g in self.NK:
                    if g in cand:
                        continue
                    r = g - 8 * pdir(c)
                    if r in EPR and r in cand:
                        self.add([-TO[g], EPR[r]], 'R3')
                    else:
                        self.add([-TO[g]], 'R3')

    def add_material(self, spec):
        for key, bound in spec.items():
            if key == 'all':
                cs, ps = [0, 1], list(range(5))
            else:
                assert key[0] in 'WB'
                cs = [0] if key[0] == 'W' else [1]
                ps = list(range(5)) if len(key) == 1 else [TN.index(ch) for ch in key[1:]]
            lits = [self.X[0][s][5 * c + p] for s in self.NK for c in cs for p in ps]
            self.atmost_generic(lits, bound, 'material')

    def atmost_generic(self, lits, k, grp):
        n = len(lits)
        if k >= n:
            return
        if k == 0:
            for l in lits:
                self.add([-l], grp)
            return
        s = [[self.v() for _ in range(k)] for _ in range(n)]
        for i in range(n):
            x = lits[i]
            self.add([-x, s[i][0]], grp)
            if i > 0:
                for j in range(k):
                    self.add([-s[i - 1][j], s[i][j]], grp)
                for j in range(1, k):
                    self.add([-x, -s[i - 1][j - 1], s[i][j]], grp)
                self.add([-x, -s[i - 1][k - 1]], grp)
            else:
                for j in range(1, k):
                    self.add([-s[0][j]], grp)

    def pin_start(self, fen):
        import chess
        b = chess.Board(fen)
        assert b.king(chess.WHITE) == self.K[0] and b.king(chess.BLACK) == self.K[1]
        for s in self.NK:
            pc = b.piece_at(s)
            k = EMP if pc is None else 5 * (0 if pc.color else 1) + 'pnbrq'.index(pc.symbol().lower())
            self.add([self.X[0][s][k]], 'pin')
        for s, v in self.EPS[0].items():
            self.add([v if b.ep_square == s else -v], 'pin')

    def pin_line(self, moves, shift=0):
        for t0, (f, g, pr) in enumerate(moves):
            t = t0 + shift
            if t >= self.n:
                break
            self.add([self.FR[t][f]], 'pin')
            self.add([self.TO[t][g]], 'pin')
            if pr is not None:
                self.add([self.RT[t][pr]], 'pin')

    def dimacs(self, path):
        with open(path, 'w') as fh:
            fh.write('p cnf %d %d\n' % (self.nv, len(self.cls)))
            fh.write(''.join(' '.join(map(str, c)) + ' 0\n' for c in self.cls))

    def meta(self):
        return {'K': self.K, 'n': self.n, 'first': self.first, 'NK': self.NK,
                'X0': {str(s): self.X[0][s] for s in self.NK},
                'FR': [{str(s): v for s, v in d.items()} for d in self.FR],
                'TO': [{str(s): v for s, v in d.items()} for d in self.TO],
                'RT': self.RT, 'MP': self.MP, 'CAP': self.CAP,
                'EPS0': {str(s): v for s, v in self.EPS[0].items()},
                'EPR': [{str(s): v for s, v in d.items()} for d in self.EPR],
                'A': [[{str(s): v for s, v in d.items()} for d in AX] for AX in self.A],
                'nv': self.nv, 'nc': len(self.cls), 'groups': dict(self.groups)}

def decode(meta, model):
    import chess
    pos = {}
    for s in meta['NK']:
        xs = meta['X0'][str(s)]
        ks = [k for k in range(11) if xs[k] in model]
        assert len(ks) == 1
        k = ks[0]
        if k != EMP:
            c, p = divmod(k, 5)
            pos[s] = chess.Piece('PNBRQ'.index(TN[p]) + 1, c == 0)
    b = chess.Board(None)
    for s, pc in pos.items():
        b.set_piece_at(s, pc)
    b.set_piece_at(meta['K'][0], chess.Piece(chess.KING, True))
    b.set_piece_at(meta['K'][1], chess.Piece(chess.KING, False))
    b.turn = (meta['first'] == 0)
    eps = [int(s) for s, v in meta['EPS0'].items() if v in model]
    b.ep_square = eps[0] if eps else None
    fen = b.fen(en_passant='fen')
    moves = []
    for t in range(meta['n']):
        f = [int(s) for s, v in meta['FR'][t].items() if v in model]
        g = [int(s) for s, v in meta['TO'][t].items() if v in model]
        rt = [p for p in range(5) if meta['RT'][t][p] in model]
        mp = [p for p in range(5) if meta['MP'][t][p] in model]
        assert len(f) == 1 and len(g) == 1 and len(rt) == 1 and len(mp) == 1
        promo = None
        if mp[0] == P and rt[0] != P:
            promo = 'nbrq'[rt[0] - 1]
        moves.append(chess.square_name(f[0]) + chess.square_name(g[0]) + (promo or ''))
    return fen, moves

def replay(fen, moves):
    import chess
    b = chess.Board(fen)
    san, caps, ok, why = [], 0, True, ''
    for i, u in enumerate(moves):
        mv = chess.Move.from_uci(u)
        if mv not in b.legal_moves:
            ok, why = False, 'ply %d %s illegal' % (i, u)
            break
        if b.piece_type_at(mv.from_square) == chess.KING:
            ok, why = False, 'king move'
            break
        if b.is_capture(mv):
            caps += 1
        san.append(b.san(mv))
        b.push(mv)
        if not b.is_check():
            ok, why = False, 'ply %d %s gives no check' % (i, u)
            break
    return {'ok': ok, 'why': why, 'captures': caps, 'san': san, 'plies': len(san)}

def parse_args(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--kw', required=True)
    ap.add_argument('--kb', required=True)
    ap.add_argument('-n', type=int, required=True)
    ap.add_argument('--first', choices=['w', 'b'], default='w')
    ap.add_argument('--cap', default='0', help="'any', or 'N' (at most N), or '=N' (exactly N)")
    ap.add_argument('--start', choices=['c0', 'relaxed'], default='c0')
    ap.add_argument('--no-ep', action='store_true')
    ap.add_argument('--no-promo', action='store_true')
    ap.add_argument('--init-check', action='store_true')
    ap.add_argument('--no-redundant', action='store_true')
    ap.add_argument('--no-single-check', action='store_true')
    ap.add_argument('--pin-pgn', help='pin start FEN and moves of a PGN (calibration)')
    ap.add_argument('--pin-moves-only', action='store_true', help='with --pin-pgn: pin the moves only')
    ap.add_argument('--pin-plies', type=int, default=None, help='pin only the first k plies')
    ap.add_argument('--pin-offset', type=int, default=0, help='skip the first j plies of the PGN')
    ap.add_argument('--pin-shift', type=int, default=0, help='pin PGN move i to ply i+s (s free plies first; needs --pin-moves-only)')
    ap.add_argument('--material', default=None, help='JSON dict of upper bounds on start non-king men')
    ap.add_argument('--lemma-run', type=int, default=None, help='add: every window of K+1 plies has a capture (uses B(0)<=K)')
    ap.add_argument('-o', '--out', required=True)
    return ap.parse_args(argv)

def build_from_args(a):
    import chess, chess.pgn
    cap = a.cap
    if cap == 'any':
        capmode, m = 'any', 0
    elif cap.startswith('='):
        capmode, m = 'exact', int(cap[1:])
    else:
        capmode, m = 'atmost', int(cap)
    pin_fen = pin_moves = None
    if a.pin_pgn:
        g = chess.pgn.read_game(open(a.pin_pgn))
        b = g.board()
        mv = list(g.mainline_moves())
        for i in range(a.pin_offset):
            b.push(mv[i])
        mv = mv[a.pin_offset:]
        if a.pin_plies is not None:
            mv = mv[:a.pin_plies]
        if not a.pin_moves_only:
            pin_fen = b.fen(en_passant='fen')
        pin_moves = [(m_.from_square, m_.to_square, (m_.promotion - 1) if m_.promotion else None) for m_ in mv]
    mat = json.loads(a.material) if a.material else None
    return Enc(psq(a.kw), psq(a.kb), a.n, 0 if a.first == 'w' else 1, capmode, m, a.start,
               not a.no_ep, not a.no_promo, a.init_check, not a.no_redundant, pin_fen, pin_moves,
               not a.no_single_check, mat, a.lemma_run, a.pin_shift)

if __name__ == '__main__':
    a = parse_args()
    e = build_from_args(a)
    e.dimacs(a.out)
    md = e.meta()
    md['args'] = vars(a)
    md['encoder_sha256'] = hashlib.sha256(open(__file__, 'rb').read()).hexdigest()
    json.dump(md, open(a.out + '.json', 'w'))
    print(json.dumps({'vars': e.nv, 'clauses': len(e.cls), 'groups': dict(e.groups)}))
