import sys, random, json, time
import chess
import enc

PM = {'N': chess.KNIGHT, 'B': chess.BISHOP, 'R': chess.ROOK, 'Q': chess.QUEEN}


def assign(e, b):
    v = {}
    for q, d in e.x.items():
        pc = b.piece_at(q)
        k = '.' if pc is None else pc.symbol()
        for kk, var in d.items():
            v[var] = (kk == k)
    epf = None
    if b.ep_square is not None:
        epf = chess.square_file(b.ep_square)
    for f, var in e.ep.items():
        v[var] = (f == epf)
    for name, var in e.cr.items():
        v[var] = bool(b.castling_rights & (chess.BB_H1 if name == 'K' else chess.BB_A1))
    inv = {g: k for k, g in e.cache.items()}
    for g in sorted(inv):
        op, L = inv[g]
        vals = [v[l] if l > 0 else not v[-l] for l in L]
        v[g] = all(vals) if op == 'and' else any(vals)
    return v


def val(v, l):
    if l is True or l is False:
        return l
    return v[l] if l > 0 else not v[-l]


def test(b, thr=0, allcheck=False, expect_sat=None):
    kw, kb = b.king(chess.WHITE), b.king(chess.BLACK)
    chk = b.is_check()
    e = enc.build(kw, kb, chk, thr, allcheck)
    v = assign(e, b)
    bad = [c for c in e.cls if not any(val(v, l) for l in c)]
    legal = {}
    for key, T, lg, ck, w in e.moves:
        if val(v, lg):
            s, t, pr = key
            m = chess.Move(s, t, PM[pr] if pr else None)
            legal[m] = val(v, ck)
    py = {m: b.gives_check(m) for m in b.legal_moves}
    return bad, legal, py


def rand_positions(n, seed):
    rnd = random.Random(seed)
    out = []
    while len(out) < n:
        b = chess.Board()
        for _ in range(rnd.randint(0, 120)):
            ms = list(b.legal_moves)
            if not ms:
                break
            caps = [m for m in ms if b.is_capture(m) or m.promotion or b.gives_check(m) or b.is_castling(m) or b.is_en_passant(m)]
            b.push(rnd.choice(caps if caps and rnd.random() < 0.5 else ms))
        if b.turn == chess.WHITE and not b.is_game_over():
            out.append(chess.Board(b.fen()))
    return out


def rand_placements(n, seed, edge=False):
    rnd = random.Random(seed)
    out = []
    pcs = 'PNBRQpnbrq'
    while len(out) < n:
        b = chess.Board(None)
        kw, kb = rnd.sample(range(64), 2)
        if edge:
            u = rnd.random()
            if u < 0.35:
                kw = chess.E1
            elif u < 0.6:
                kw = chess.square(rnd.randrange(8), 4)
            if rnd.random() < 0.3:
                kb = rnd.choice([q for q in range(64) if chess.square_distance(q, kw) == 2] or [kb])
        if kw == kb or chess.square_distance(kw, kb) < 2:
            continue
        b.set_piece_at(kw, chess.Piece(chess.KING, chess.WHITE))
        b.set_piece_at(kb, chess.Piece(chess.KING, chess.BLACK))
        for q in rnd.sample([q for q in range(64) if q not in (kw, kb)], rnd.randint(0, 24)):
            s = rnd.choice('PPQRBNqrbp' if edge and chess.square_rank(q) == 6 else 'QRBqrbNnPp' if edge else pcs)
            if s in 'Pp' and chess.square_rank(q) in (0, 7):
                continue
            b.set_piece_at(q, chess.Piece.from_symbol(s))
        if rnd.random() < (0.9 if edge else 0.3) and kw == chess.E1:
            for c in (chess.H1, chess.A1):
                if rnd.random() < 0.7 and c != kb:
                    b.set_piece_at(c, chess.Piece(chess.ROOK, chess.WHITE))
            b.castling_rights = b.clean_castling_rights() | (chess.BB_H1 | chess.BB_A1) & b.rooks & b.occupied_co[chess.WHITE]
            b.castling_rights = b.clean_castling_rights()
        if rnd.random() < (0.8 if edge else 0.4):
            f = rnd.randrange(8)
            q5, q6, q7 = chess.square(f, 4), chess.square(f, 5), chess.square(f, 6)
            if q5 not in (kw, kb) and q6 not in (kw, kb) and q7 not in (kw, kb):
                b.set_piece_at(q5, chess.Piece(chess.PAWN, chess.BLACK))
                b.remove_piece_at(q6); b.remove_piece_at(q7)
                for df in (-1, 1):
                    if 0 <= f + df < 8 and rnd.random() < 0.7 and chess.square(f + df, 4) not in (kw, kb):
                        b.set_piece_at(chess.square(f + df, 4), chess.Piece(chess.PAWN, chess.WHITE))
                b.ep_square = q6
        b.turn = chess.WHITE
        if b.was_into_check():
            continue
        if b.is_check() and len(b.checkers()) > 2:
            continue
        ok = True
        for col in (chess.WHITE, chess.BLACK):
            men = chess.popcount(b.occupied_co[col]) - 1
            P = len(b.pieces(chess.PAWN, col))
            N, R, Q = (len(b.pieces(t, col)) for t in (chess.KNIGHT, chess.ROOK, chess.QUEEN))
            Bs = b.pieces(chess.BISHOP, col)
            lt = chess.popcount(int(Bs) & chess.BB_LIGHT_SQUARES); dk = chess.popcount(int(Bs) & chess.BB_DARK_SQUARES)
            ex = max(0, N - 2) + max(0, R - 2) + max(0, Q - 1) + max(0, lt - 1) + max(0, dk - 1)
            if men > 15 or P + ex > 8:
                ok = False
        if ok:
            out.append(b)
    return out


if __name__ == '__main__':
    mode = sys.argv[1]
    n = int(sys.argv[2]); seed = int(sys.argv[3])
    if mode == 'fens':
        P = [chess.Board(l.strip()) for l in open(sys.argv[4]) if l.strip()]
    elif mode == 'games':
        P = rand_positions(n, seed)
    elif mode == 'edge':
        P = rand_placements(n, seed, True)
    else:
        P = rand_placements(n, seed)
    st = dict(pos=0, moves=0, incheck=0, castle=0, ep=0, promo=0, checks=0, clause_viol=0, legal_mismatch=0, check_mismatch=0)
    for b in P:
        bad, legal, py = test(b)
        st['pos'] += 1
        st['moves'] += len(py)
        st['incheck'] += b.is_check()
        st['castle'] += sum(b.is_castling(m) for m in py)
        st['ep'] += sum(b.is_en_passant(m) for m in py)
        st['promo'] += sum(bool(m.promotion) for m in py)
        st['checks'] += sum(py.values())
        if bad:
            st['clause_viol'] += 1
            print('VIOL', b.fen(), bad[:3], flush=True)
        if set(legal) != set(py):
            st['legal_mismatch'] += 1
            print('LEGAL', b.fen(), sorted(map(str, set(legal) ^ set(py))), flush=True)
        else:
            mm = [m for m in py if py[m] != legal[m]]
            if mm:
                st['check_mismatch'] += 1
                print('CHECK', b.fen(), [str(m) for m in mm], flush=True)
    print(json.dumps(st), flush=True)
