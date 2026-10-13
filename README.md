# double-check

**Theorem 1.** From any legal chess position, at most 364 consecutive moves can all give check.

**Theorem 2.** If every legal move gives check, there are at most 63 legal moves. 63 is attained in a position reachable from the initial position (`data/allcheck63.pgn`).

Both are proved in Lean 4 (`lean/ChessProof/Statements.lean`, `lean/ChessProof/Final.lean`), modulo one axiom per SAT instance: `(G63 i).Unsat` for the 7,224 cases of Theorem 2 and `(R364 i).Unsat` for the 6,921 records of Theorem 1. Each formula is computed by an encoder defined in Lean; its DIMACS output has the sha256 listed in `data/`, and its LRAT proof was accepted by three independent checkers.

```
docker build -t chess . && docker run chess
docker run chess lean/check.sh
docker run chess lean/check.sh all
docker run chess python3 src/cover.py --sample all --resolve all
docker run chess python3 src/allcheck/cover63.py --sample all --resolve all
```

The first command checks every tree of the certificate, re-derives a sample of hashes and re-solves a sample. `lean/check.sh` builds the Lean proof (about 25 GB of memory), prints its axioms, checks Lean-encoded formulas against the certificate hashes (a sample, or `all`) and tests the Lean move generator against python-chess. The last two re-solve every instance (about 120 core-hours each). `lean/tests/lrat.sh <cnf> <lrat>` checks a proof with Lean's verified LRAT checker.
