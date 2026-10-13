import ChessProof.Fen
import ChessProof.All63.Enc
import ChessProof.All63.Cases
import ChessProof.All63.Assign

open Chess Chess.All63

def sqStr (q : Nat) : String :=
  (Char.ofNat ('a'.toNat + q % 8)).toString ++ toString (q / 8 + 1)

def famName : Fam → String
  | .gate => "gate"
  | .onehot => "onehot"
  | .rank => "rank"
  | .start => "start"
  | .ep => "ep"
  | .castle => "castle"
  | .material => "material"
  | .allcheck => "allcheck"
  | .thr => "thr"

def fams : List Fam := [.gate, .onehot, .rank, .start, .ep, .castle, .material, .allcheck, .thr]

def evalFen (fen : String) : String :=
  match parseFen fen with
  | none => "err"
  | some p =>
    let c := cfgOf p
    let ((rt, ms), s) := (c.build 64).run {}
    let vs := valsOf p s.defs
    let A : Assignment := fun v => if v = 0 then false else vs.getD (v - 1) false
    let good := (List.range s.defs.size).all fun i => A (i + 1) == (s.defs[i]!).val p A
    let viol := fams.map fun f => famName f ++ ":" ++
      toString ((s.cls.filter fun fc => fc.1 == f && !fc.2.sat A).size)
    let legal := legalMoves p
    let wireBad := ms.toList.countP fun (m, lg, ck) => lg.eval A != m.legal.eval A || (lg.eval A && ck.eval A != m.chk.eval A)
    let cs := c.cands rt
    let on := cs.filter fun m => m.legal.eval A
    let candBad := on.countP fun m => !(legal.contains m.mv) || m.chk.eval A != givesCheck p m.mv ||
      !(m.covers.all (legal.contains ·))
    let uncovered := legal.countP fun mv => !(on.any fun m => m.covers.contains mv)
    let wsum := on.foldl (fun a m => a + m.w) 0
    let allChk := legal.all (givesCheck p)
    s!"ok adm={admB p} turnW={p.turn == .white} good={good} wireBad={wireBad} candBad={candBad} uncovered={uncovered} wsum={wsum} len={legal.length} allcheck={allChk} " ++
      ",".intercalate viol

partial def loop (h o : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  o.putStrLn (evalFen (line.trimAsciiEnd.toString))
  o.flush
  loop h o

def main (args : List String) : IO UInt32 := do
  match args with
  | ["cnf", kw, kb, ck] =>
    (G ⟨kw.toNat!, kb.toNat!, ck == "1"⟩).writeDimacs (← IO.getStdout)
    return 0
  | ["case", i] =>
    let f := G (caseAt i.toNat!)
    if !f.wfB then
      IO.eprintln "not well-formed"
      return 2
    f.writeDimacs (← IO.getStdout)
    return 0
  | ["cases"] =>
    let o ← IO.getStdout
    for (c, i) in cases.zipIdx do
      o.putStrLn s!"{i} {sqStr c.kw} {sqStr c.kb} {if c.chk then 1 else 0}"
    return 0
  | ["eval"] =>
    loop (← IO.getStdin) (← IO.getStdout)
    return 0
  | _ => IO.eprintln "usage"; return 1
