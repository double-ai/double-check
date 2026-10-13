import ChessProof.Spec
import ChessProof.Cnf
import ChessProof.All63.Geom
import ChessProof.All63.Circuit

namespace Chess.All63

structure Cfg where
  kw : Nat
  kb : Nat
  chk : Bool
deriving DecidableEq, Repr, Inhabited

def symW : List Nat := [0, 1, 2, 3, 4]

def symB : List Nat := [5, 6, 7, 8, 9]

def EMP : Nat := 10

def A1 : Nat := 0
def B1 : Nat := 1
def C1 : Nat := 2
def D1 : Nat := 3
def E1 : Nat := 4
def F1 : Nat := 5
def G1 : Nat := 6
def H1 : Nat := 7

namespace Cfg

variable (c : Cfg)

def isK (q : Nat) : Bool := q == c.kw || q == c.kb

def xIdx (q : Nat) : Nat := q - (if c.kw < q then 1 else 0) - (if c.kb < q then 1 else 0)

def xv (q k : Nat) : Int := (1 + 11 * c.xIdx q + k : Nat)

def squares : List Nat := (List.range 64).filter fun q => !c.isK q

def p (q k : Nat) : Ex := if c.isK q then .k false else .v (c.xv q k)

def empty (q : Nat) : Ex := c.p q EMP

def has (q : Nat) (ks : List Nat) : Ex := .or (ks.map (c.p q))

def wocc (q : Nat) : Ex := if q == c.kw then .k true else c.has q symW

def clear (a b : Nat) (emp occ : List Nat) : Ex :=
  let bs := (between a b).filter (· ∉ emp)
  if bs.any (· ∈ occ) then .k false else .and (bs.map c.empty)

def att (K : Nat) (white : Bool) (k : Nat) (emp occ excl : List Nat) : Ex :=
  let bad (q : Nat) : Bool := q ∈ emp || q ∈ occ || q ∈ excl
  let sh (x : Nat) : Nat := if white then x else x + 5
  let sl := (orth ++ diag).flatMap fun d =>
    let syms := (if d ∈ orth then [3, 4] else [2, 4]).map sh
    (rayL K d).filterMap fun q => if bad q then none else some (Ex.and [c.has q syms, c.clear K q emp occ])
  let kt := (knightL K).filterMap fun q => if bad q then none else some (c.p q (sh 1))
  let pr : Int := if white then (fr K).2 - 1 else (fr K).2 + 1
  let pw := [(-1 : Int), 1].filterMap fun df =>
    match sqo ((fr K).1 + df) pr with
    | some q => if bad q then none else some (c.p q (sh 0))
    | none => none
  let kg : List Ex := if cheb k K == 1 then [.k true] else []
  .or (sl ++ kt ++ pw ++ kg)

def attB (K : Nat) (emp occ excl : List Nat) : Ex := c.att K false c.kb emp occ excl

def attW (K : Nat) (emp occ excl : List Nat) (k : Nat := c.kw) : Ex := c.att K true k emp occ excl

def direct (t T : Nat) (emp occ : List Nat) : Ex :=
  let K := c.kb
  if T == 1 then .k (cheb t K ≤ 2 && (knightL t).contains K)
  else if T == 0 then .k ((fr K).2 == (fr t).2 + 1 && ((fr K).1 - (fr t).1).natAbs == 1)
  else
    match direction t K with
    | none => .k false
    | some d =>
      if (T == 3 && d ∉ orth) || (T == 2 && d ∉ diag) then .k false
      else c.clear t K emp occ

def targets (q T : Nat) : List Nat :=
  let out := if T == 1 then knightL q
    else (if T == 3 then orth else if T == 2 then diag else orth ++ diag).flatMap (rayL q)
  out.filter fun t => !c.isK t

end Cfg

def kindOf : Nat → Kind
  | 0 => .pawn
  | 1 => .knight
  | 2 => .bishop
  | 3 => .rook
  | 4 => .queen
  | _ => .king

structure Cand where
  src : Nat
  dst : Nat
  promo : Option Nat
  T : Nat
  ep : Option Nat
  pseudo : Ex
  legal : Ex
  chk : Ex
  w : Nat
  skip : Bool

def Cand.mv (m : Cand) : Move := ⟨toSq m.src, toSq m.dst, m.promo.map kindOf⟩

structure Rights where
  ep : List (Nat × Int)
  cr : List (Bool × Int)

namespace Cfg

variable (c : Cfg)

def mkMove (q t : Nat) (pr : Option Nat) (T : Nat) (pseudo : Ex) (ep : Option Nat) (w : Nat) : Cand :=
  let emp := q :: ep.toList
  { src := q, dst := t, promo := pr, T := T, ep := ep, pseudo := pseudo, w := w, skip := true
    legal := .and [pseudo, .not (c.attB c.kw emp [t] [t])]
    chk := .or [c.direct t (pr.getD T) emp [], c.attW c.kb emp [t] [t]] }

def mkPawn (q t : Nat) (pseudo : Ex) : List Cand :=
  if (fr t).2 == 7 then
    [(1, 4), (2, 0), (3, 0), (4, 0)].map fun (T, w) => c.mkMove q t (some T) 0 pseudo none w
  else [c.mkMove q t none 0 pseudo none 1]

def pieceCands (q : Nat) : List Cand :=
  [1, 2, 3, 4].flatMap fun T =>
    (c.targets q T).map fun t =>
      let pseudo := if T == 1 then Ex.and [c.p q T, .not (c.wocc t)]
        else Ex.and [c.p q T, c.clear q t [] [], .not (c.wocc t)]
      c.mkMove q t none T pseudo none 1

def pawnCands (r : Rights) (q : Nat) : List Cand :=
  let f := (fr q).1
  let rk := (fr q).2
  if rk == 0 || rk == 7 then [] else
  let t := (sqo f (rk + 1)).getD 0
  let t3 := (sqo f 3).getD 0
  let pushes :=
    if c.isK t then [] else
      c.mkPawn q t (.and [c.p q 0, c.empty t]) ++
      (if rk == 1 && !c.isK t3 then c.mkPawn q t3 (.and [c.p q 0, c.empty t, c.empty t3]) else [])
  let caps := [(-1 : Int), 1].flatMap fun df =>
    match sqo (f + df) (rk + 1) with
    | none => []
    | some t =>
      if c.isK t then [] else
      c.mkPawn q t (.and [c.p q 0, c.has t symB]) ++
      (match (if rk == 4 then r.ep.lookup (f + df).toNat else none) with
       | some v => [c.mkMove q t none 0 (.and [c.p q 0, .v v]) (sqo (f + df) 4) 1]
       | none => [])
  pushes ++ caps

def kingCands : List Cand :=
  (List.range 64).filterMap fun t =>
    if cheb c.kw t == 1 && cheb c.kb t > 1 then
      let pseudo := Ex.not (c.wocc t)
      some { src := c.kw, dst := t, promo := none, T := 5, ep := none, pseudo := pseudo, w := 1, skip := false
             legal := .and [pseudo, .not (c.attB t [c.kw] [] [t])]
             chk := c.attW c.kb [c.kw] [t] [t] t }
    else none

def castleK (v : Int) : Cand where
  src := E1
  dst := G1
  promo := none
  T := 5
  ep := none
  pseudo := .k true
  w := 1
  skip := false
  legal := .and [.v v, c.empty F1, c.empty G1, .not (c.attB E1 [E1] [] []), .not (c.attB F1 [E1] [] []),
    .not (c.attB G1 [E1, H1] [F1] [])]
  chk := .or [c.direct F1 3 [E1, H1] [G1], c.attW c.kb [E1, H1] [F1, G1] [F1, G1] G1]

def castleQ (v : Int) : Cand where
  src := E1
  dst := C1
  promo := none
  T := 5
  ep := none
  pseudo := .k true
  w := 1
  skip := false
  legal := .and [.v v, c.empty B1, c.empty C1, c.empty D1, .not (c.attB E1 [E1] [] []),
    .not (c.attB D1 [E1] [] []), .not (c.attB C1 [E1, A1] [D1] [])]
  chk := .or [c.direct D1 3 [E1, A1] [C1], c.attW c.kb [E1, A1] [D1, C1] [D1, C1] C1]

def castleCands (r : Rights) : List Cand :=
  (r.cr.lookup true).toList.map c.castleK ++ (r.cr.lookup false).toList.map c.castleQ

def cands (r : Rights) : List Cand :=
  c.squares.flatMap (fun q => c.pieceCands q ++ c.pawnCands r q) ++ c.kingCands ++ c.castleCands r

def initPhase : M Unit := do
  for q in c.squares do
    let mut L : Array Int := #[]
    for k in List.range 11 do
      let v ← newVar (.x q k)
      L := L.push v
    emit .onehot L
    for i in List.range 11 do
      for j in List.range' (i + 1) (10 - i) do
        emit .onehot #[-L[i]!, -L[j]!]
    if (fr q).2 == 0 || (fr q).2 == 7 then
      emit .rank #[-L[0]!]
      emit .rank #[-L[5]!]

def startPhase : M Unit := do
  require .start (← compile (.not (c.attW c.kb [] [] [])))
  let a ← compile (c.attB c.kw [] [] [])
  require .start (if c.chk then a else a.neg)

def epPhase : M (List (Nat × Int)) := do
  let mut ep : List (Nat × Int) := []
  for f in List.range 8 do
    let q5 := f + 32
    let q6 := f + 40
    let q7 := f + 48
    if c.isK q5 || c.isK q6 || c.isK q7 then continue
    let v ← newVar (.ep f)
    ep := ep ++ [(f, (v : Int))]
    emit .ep #[-v, c.xv q5 5]
    emit .ep #[-v, c.xv q6 EMP]
    emit .ep #[-v, c.xv q7 EMP]
  let E := ep.map (·.2)
  for i in List.range E.length do
    for j in List.range' (i + 1) (E.length - 1 - i) do
      emit .ep #[-E[i]!, -E[j]!]
  return ep

def crPhase : M (List (Bool × Int)) := do
  let mut cr : List (Bool × Int) := []
  if c.kw == E1 && !c.chk then
    for (ks, rq) in [(true, H1), (false, A1)] do
      if rq != c.kb then
        let v ← newVar (.cr ks)
        cr := cr ++ [(ks, (v : Int))]
        emit .castle #[-v, c.xv rq 3]
  return cr

def materialPhase (white : Bool) : M Unit := do
  let sh (x : Nat) : Nat := if white then x else x + 5
  let sq := c.squares
  let lit (q k : Nat) : Wire := .lit (c.xv q (sh k))
  atmost .material (sq.flatMap fun q => (List.range 5).map (lit q)) 15
  let pawns := sq.map fun q => lit q 0
  let mut ex : List Wire := []
  for (k, base) in [(1, 2), (3, 2), (4, 1)] do
    let cnt ← counter (sq.map fun q => lit q k) 15
    ex := ex ++ (cnt.toList.drop (base + 1))
  for colour in [0, 1] do
    let cnt ← counter ((sq.filter fun q => ((fr q).1 + (fr q).2) % 2 == colour).map fun q => lit q 2) 15
    ex := ex ++ (cnt.toList.drop 2)
  atmost .material (pawns ++ ex) 8

def compileCand (m : Cand) : M (Cand × Wire × Wire) := do
  let ps ← compile m.pseudo
  if m.skip && ps == .ff then return (m, .ff, .ff)
  let lg ← compile m.legal
  let ck ← compile m.chk
  return (m, lg, ck)

def movesPhase (r : Rights) : M (Array (Cand × Wire × Wire)) :=
  (c.cands r).toArray.mapM compileCand

end Cfg

def countPhase (thr : Nat) (allcheck : Bool) (ms : Array (Cand × Wire × Wire)) : M Unit := do
  let mut cnt : List Wire := []
  for (m, lg, ck) in ms do
    if lg == .ff then continue
    if allcheck && ck != .tt then emitW .allcheck [lg.neg, ck]
    cnt := cnt ++ List.replicate m.w lg
  atleast .thr cnt thr

namespace Cfg

variable (c : Cfg)

def build (thr : Nat) (allcheck : Bool := true) : M (Rights × Array (Cand × Wire × Wire)) := do
  c.initPhase
  c.startPhase
  let ep ← c.epPhase
  let cr ← c.crPhase
  c.materialPhase true
  c.materialPhase false
  let r : Rights := ⟨ep, cr⟩
  let ms ← c.movesPhase r
  countPhase thr allcheck ms
  return (r, ms)

def encode (thr : Nat) (allcheck : Bool := true) : St := ((c.build thr allcheck).run {}).2

def rights (thr : Nat) : Rights := ((c.build thr).run {}).1.1

end Cfg

def G (c : Cfg) : Cnf := (c.encode 64).toCnf

end Chess.All63
