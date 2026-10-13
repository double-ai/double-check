import random
import subprocess
import sys
from pathlib import Path

import chess

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "spectest"
ALLCHECK = ROOT.parent / "data" / "allcheck" / "fens.txt"
P63 = "1Q1Qn1b1/Q3P2q/2k2r2/Q3QN2/pP1Q1P2/b1NKB2r/2Rn2R1/1q1q3B w - - 11 96"

KIWIPETE = "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1"
POS3 = "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1"
POS4 = "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1"
POS4M = "r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ - 0 1"
POS5 = "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8"
POS6 = "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10"

PERFT = [
    ("initial", None, 1, 20),
    ("initial", None, 2, 400),
    ("initial", None, 3, 8902),
    ("initial", None, 4, 197281),
    ("kiwipete", KIWIPETE, 3, 97862),
    ("pos3", POS3, 3, 2812),
    ("pos3", POS3, 5, 674624),
    ("pos4", POS4, 3, 9467),
    ("pos4m", POS4M, 3, 9467),
    ("pos5", POS5, 3, 62379),
    ("pos6", POS6, 3, 89890),
]


def perft(b: chess.Board, d: int) -> int:
    if d == 0:
        return 1
    if d == 1:
        return b.legal_moves.count()
    n = 0
    for m in list(b.legal_moves):
        b.push(m)
        n += perft(b, d - 1)
        b.pop()
    return n


def ref_moves(b: chess.Board) -> set[str]:
    return {m.uci() + ("+" if b.gives_check(m) else "") for m in b.legal_moves}


def features(b: chess.Board) -> set[str]:
    f = set()
    if b.is_check():
        f.add("check")
    for m in b.legal_moves:
        if b.is_en_passant(m):
            f.add("ep")
        if b.is_castling(m):
            f.add("castle")
        if m.promotion:
            f.add("promo")
    if b.has_castling_rights(chess.WHITE) or b.has_castling_rights(chess.BLACK):
        f.add("rights")
    if b.ep_square is not None:
        f.add("epsq")
    if b.legal_moves.count() == 0:
        f.add("terminal")
    return f


def pick(b: chess.Board, rng: random.Random) -> chess.Move:
    ms = list(b.legal_moves)
    special = [m for m in ms if b.is_castling(m) or b.is_en_passant(m) or m.promotion]
    if special and rng.random() < 0.5:
        return rng.choice(special)
    pawn = [m for m in ms if b.piece_type_at(m.from_square) == chess.PAWN]
    if pawn and rng.random() < 0.35:
        return rng.choice(pawn)
    checks = [m for m in ms if b.gives_check(m)]
    if checks and rng.random() < 0.15:
        return rng.choice(checks)
    return rng.choice(ms)


def pick_rights(b: chess.Board, rng: random.Random) -> chess.Move:
    ms = list(b.legal_moves)
    rk = [m for m in ms if b.piece_type_at(m.from_square) in (chess.ROOK, chess.KING) or b.piece_type_at(m.to_square) == chess.ROOK]
    if rk and rng.random() < 0.4:
        return rng.choice(rk)
    return pick(b, rng)


HAND = [
    "e2e4 e7e5 g1f3 g8f6 f1c4 f8c5 h1g1 h8g8 g1h1 g8h8",
    "d2d4 d7d5 b1c3 b8c6 c1f4 c8f5 d1d2 d8d7 a1b1 a8b8 b1a1 b8a8",
    "e2e4 e7e5 g1f3 g8f6 f1c4 f8c5 e1f1 e8f8 f1e1 f8e8",
    "b2b3 g7g5 c1b2 g8f6 b2f6 h7h5 f6h8 f8g7 a2a3 a7a5 a3a4 a8a6 b1a3 a6h6 a1b1 h6h8 b1a1",
    "e2e4 d7d5 e4e5 f7f5 e5f6 e7e5 d2d4 e5d4 c2c4 d4c3",
    "e2e4 a7a6 e4e5 d7d5",
]


def sample(rng: random.Random, games: int):
    starts = [chess.STARTING_FEN, KIWIPETE, POS3, POS4, POS4M, POS5, POS6]
    pool = []
    lines = []
    for g in range(games):
        start = chess.STARTING_FEN if g % 2 == 0 else rng.choice(starts)
        b = chess.Board(start)
        for _ in range(rng.randint(20, 250)):
            if b.is_game_over(claim_draw=False):
                break
            b.push(pick(b, rng))
            pool.append((b.fen(), features(b)))
        if start == chess.STARTING_FEN:
            lines.append([m.uci() for m in b.move_stack])
    return pool, lines


def run(cmds: list[str]) -> list[str]:
    out = subprocess.run([str(EXE)], input="\n".join(cmds) + "\n", capture_output=True, text=True, check=True).stdout
    res = out.splitlines()
    assert len(res) == len(cmds), (len(res), len(cmds))
    return res


def parse_moves(line: str) -> set[str] | None:
    if not line.startswith("ok"):
        return None
    return set(line[3:].split())


def main() -> int:
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 20261011)
    bad = 0

    cmds = [f"perft {d}" + (f" {fen}" if fen else "") for _, fen, d, _ in PERFT]
    got = run(cmds)
    for (name, fen, d, known), line in zip(PERFT, got):
        ref = perft(chess.Board(fen) if fen else chess.Board(), d)
        lean = int(line[3:]) if line.startswith("ok") else -1
        ok = lean == ref == known
        bad += not ok
        print(f"perft {name} d{d}: lean={lean} python-chess={ref} known={known} {'OK' if ok else 'MISMATCH'}")

    pool, lines = sample(rng, 2500)
    rng.shuffle(pool)
    rare = [x for x in pool if x[1] & {"ep", "castle", "epsq", "terminal"}]
    tagged = [x for x in pool if x[1] & {"check", "promo"}]
    plain = [x for x in pool if not x[1] & {"check", "ep", "castle", "promo", "terminal"}]
    seen = set()
    chosen = []
    for fen, f in rare[:1500] + tagged[:3500] + plain[:3000]:
        if fen not in seen:
            seen.add(fen)
            chosen.append((fen, f))

    def compare(label: str, fens: list[str]) -> tuple[int, int, int]:
        nb = 0
        nm = 0
        res = run([f"moves {fen}" for fen in fens])
        for fen, line in zip(fens, res):
            ref = ref_moves(chess.Board(fen))
            nm += len(ref)
            if parse_moves(line) != ref:
                nb += 1
                if nb <= 10:
                    lean = parse_moves(line) or set()
                    print(f"  MISMATCH {label}: {fen}\n    lean-only {sorted(lean - ref)}\n    ref-only {sorted(ref - lean)}")
        return nb, len(fens), nm

    fens = [f for f, _ in chosen]
    nb, n, nm = compare("random", fens)
    bad += nb
    cnt = {k: sum(k in f for _, f in chosen) for k in ["check", "ep", "castle", "promo", "rights", "epsq", "terminal"]}
    print(f"random positions: {n} positions, {nm} moves, mismatches={nb}; features {cnt}")

    fens_full = [chess.Board(f).fen(en_passant="fen") for f in fens]
    nb, n, nm = compare("random-fen-ep", fens_full)
    bad += nb
    print(f"random positions (ep field always written): {n} positions, mismatches={nb}")

    games = [ln.split() for ln in HAND]
    for _ in range(500):
        b = chess.Board()
        for _ in range(rng.randint(20, 160)):
            if b.is_game_over(claim_draw=False):
                break
            b.push(pick_rights(b, rng))
        games.append([m.uci() for m in b.move_stack])
    res = run(["game " + " ".join(g) for g in games])
    nb = 0
    npos = 0
    castles = 0
    for g, line in zip(games, res):
        parts = line[3:].split(" | ") if line.startswith("ok") else []
        b = chess.Board()
        refs = []
        for u in [*g, None]:
            refs.append(ref_moves(b))
            castles += any(b.is_castling(m) for m in b.legal_moves)
            if u:
                b.push_uci(u)
        npos += len(refs)
        lean = [set(x.split()) for x in parts]
        if lean != refs:
            nb += 1
            if nb <= 10:
                print(f"  MISMATCH game: {' '.join(g)}")
    bad += nb
    print(f"full game traces from initial (rights-stress): {len(games)} games, {npos} positions, {castles} with castling legal, mismatches={nb}")

    sel = rng.sample(lines, min(600, len(lines)))
    cuts = []
    for ln in sel:
        k = rng.randint(1, len(ln))
        cuts.append(ln[:k])
    res = run(["line " + " ".join(c) for c in cuts])
    nb = 0
    plies = 0
    for c, line in zip(cuts, res):
        b = chess.Board()
        for u in c:
            b.push_uci(u)
        plies += len(c)
        if parse_moves(line) != ref_moves(b):
            nb += 1
            if nb <= 10:
                print(f"  MISMATCH line: {' '.join(c)}")
    bad += nb
    print(f"replayed game prefixes from initial: {len(cuts)} lines, {plies} plies, mismatches={nb}")

    sub = rng.sample(fens, 300)
    res = run([f"perft 2 {fen}" for fen in sub])
    nb = 0
    nodes = 0
    for fen, line in zip(sub, res):
        ref = perft(chess.Board(fen), 2)
        nodes += ref
        if line != f"ok {ref}":
            nb += 1
            if nb <= 10:
                print(f"  MISMATCH perft2: {fen} lean={line} ref={ref}")
    bad += nb
    print(f"perft depth 2 on sampled positions: {len(sub)} positions, {nodes} leaves, mismatches={nb}")

    ac = [ln.strip() for ln in ALLCHECK.read_text().splitlines() if ln.strip()]
    nb, n, nm = compare("allcheck", ac)
    bad += nb
    allchk = sum(all(x.endswith("+") for x in ref_moves(chess.Board(f))) for f in ac)
    print(f"allcheck fens: {n} positions, {nm} moves, mismatches={nb}, all-check per python-chess={allchk}")

    line = run([f"moves {P63}"])[0]
    lean = parse_moves(line) or set()
    ref = ref_moves(chess.Board(P63))
    ok = lean == ref and len(lean) == 63 and all(x.endswith("+") for x in lean)
    bad += not ok
    print(f"63 position: lean legal={len(lean)} checks={sum(x.endswith('+') for x in lean)} python-chess legal={len(ref)} {'OK' if ok else 'MISMATCH'}")

    print(f"TOTAL MISMATCHES: {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
