import ChessProof.Spec
import ChessProof.C364.Formula

namespace Chess.C364.Enc

open Chess Chess.C364.Fm

def P : Nat := 0
def N : Nat := 1
def B : Nat := 2
def R : Nat := 3
def Q : Nat := 4
def EMP : Nat := 10

def fl (s : Nat) : Int := (s % 8 : Nat)
def rk (s : Nat) : Int := (s / 8 : Nat)
def onb (f r : Int) : Bool := 0 ≤ f && f < 8 && 0 ≤ r && r < 8
def sqOf (f r : Int) : Nat := (f + 8 * r).toNat
def pdir (c : Nat) : Int := if c = 0 then 1 else -1

def orth : List (Int × Int) := [(1, 0), (-1, 0), (0, 1), (0, -1)]
def diag : List (Int × Int) := [(1, 1), (1, -1), (-1, 1), (-1, -1)]

def between (a b : Nat) : Option (List Nat) :=
  let df := fl b - fl a
  let dr := rk b - rk a
  if df = 0 ∧ dr = 0 then none
  else if df ≠ 0 ∧ dr ≠ 0 ∧ df.natAbs ≠ dr.natAbs then none
  else
    let k := max df.natAbs dr.natAbs
    some ((List.range (k - 1)).map fun (i : Nat) => sqOf (fl a + df.sign * ((i : Int) + 1)) (rk a + dr.sign * ((i : Int) + 1)))

def btw (a b : Nat) : List Nat := (between a b).getD []

def pawnAttacks (c s : Nat) : List Nat :=
  let r := rk s + pdir c
  [-1, 1].filterMap fun df =>
    let f := fl s + df
    if onb f r then some (sqOf f r) else none

def attacksGeom (p c s k : Nat) : Bool :=
  if p = P then (pawnAttacks c s).contains k
  else
    let df := (fl k - fl s).natAbs
    let dr := (rk k - rk s).natAbs
    if p = N then (df == 1 && dr == 2) || (df == 2 && dr == 1)
    else
      match between s k with
      | none => false
      | some _ =>
        let o := df == 0 || dr == 0
        if p = R then o else if p = B then !o else true

inductive Sem where
  | x (t s k : Nat)
  | fr (t s : Nat)
  | to (t s : Nat)
  | mp (t p : Nat)
  | rt (t p : Nat)
  | cap (t : Nat)
  | promo (t : Nat)
  | eps (t s : Nat)
  | epr (t r : Nat)
  | att (t x s : Nat)
  | clear (t : Nat) (ss : List Nat)
  | ch (t s : Nat)
deriving Repr, Inhabited, DecidableEq

inductive Role where
  | sem (r : Sem)
  | conj (rs : List Sem)
  | ladder (rs : List Sem) (i : Nat)
  | count (rs : List Sem) (i j : Nat)
deriving Repr, Inhabited, DecidableEq

inductive Fam where
  | onehot | clear | attack | ep | move1 | source | dest | geom | transit | pawn | cap | promo
  | update | frame | start | check | legal | capcount | r1 | r2 | r3 | r4
deriving Repr, Inhabited, DecidableEq

structure Alloc where
  nv : Nat
  roles : Array Role

abbrev AM := StateM Alloc

def fresh (r : Role) : AM Int :=
  modifyGet fun a => (((a.nv + 1 : Nat) : Int), { nv := a.nv + 1, roles := a.roles.push r })

def freshMany (rs : List Role) : AM (List Int) := rs.mapM fresh

structure Cfg where
  kw : Nat
  kb : Nat
  n : Nat
  m : Nat

def Cfg.K (g : Cfg) (x : Nat) : Nat := if x = 0 then g.kw else g.kb

def Cfg.isK (g : Cfg) (s : Nat) : Bool := s == g.kw || s == g.kb

def Cfg.NK (g : Cfg) : List Nat := (List.range 64).filter fun s => !g.isK s

def Cfg.col (_ : Cfg) (t : Nat) : Nat := t % 2

def Cfg.ray (g : Cfg) (x : Nat) (d : Int × Int) : List Nat :=
  let k := g.K x
  let o := g.K (1 - x)
  let rec go : Nat → Int → Int → List Nat
    | 0, _, _ => []
    | fuel + 1, f, r =>
      if onb f r then
        let s := sqOf f r
        if s = o then [] else s :: go fuel (f + d.1) (r + d.2)
      else []
  go 8 (fl k + d.1) (rk k + d.2)

def Cfg.raySquares (g : Cfg) (x : Nat) : List Nat := (orth ++ diag).flatMap (g.ray x)

def Cfg.cand (g : Cfg) (x : Nat) (s : Nat) : Bool :=
  (g.raySquares x).contains s ||
    (!g.isK s && (attacksGeom N (1 - x) s (g.K x) || attacksGeom P (1 - x) s (g.K x)))

def Cfg.allowed (g : Cfg) (c f t : Nat) : List Nat :=
  let df := fl t - fl f
  let dr := rk t - rk f
  let d := pdir c
  let bt := between f t
  let kn := (df.natAbs == 1 && dr.natAbs == 2) || (df.natAbs == 2 && dr.natAbs == 1)
  let sl := match bt with
    | some l => !l.any g.isK
    | none => false
  let o := df == 0 || dr == 0
  let pawn :=
    (df == 0 && dr == d) ||
    (df == 0 && dr == 2 * d && rk f == (if c = 0 then 1 else 6) && !g.isK (sqOf (fl f) (rk f + d))) ||
    (df.natAbs == 1 && dr == d)
  [(P, pawn), (N, kn), (B, sl && !o), (R, sl && o), (Q, sl)].filterMap fun (p, b) => if b then some p else none

def pairs : List Int → List (Int × Int)
  | [] => []
  | a :: l => l.map (fun b => (a, b)) ++ pairs l

def amoAlloc (rs : List Sem) : AM (List Int) :=
  if rs.length ≤ 8 then pure []
  else freshMany ((List.range (rs.length - 1)).map fun i => .ladder rs i)

def amoCls (lits lad : List Int) : List Clause :=
  if lits.length ≤ 8 then (pairs lits).map fun (a, b) => [-a, -b]
  else
    (List.range lits.length).flatMap fun i =>
      let x := lits.getD i 0
      if i + 1 < lits.length then
        let s := lad.getD i 0
        if i = 0 then [[-x, s]] else
          let sp := lad.getD (i - 1) 0
          [[-x, s], [-sp, s], [-x, -sp]]
      else [[-x, -(lad.getD (i - 1) 0)]]

def tag (f : Fam) (cs : List Clause) : List (Clause × Fam) := cs.map fun c => (c, f)

structure AttEntry where
  s : Nat
  a : Int
  conjs : List (List Int × Option Int)
deriving Inhabited

structure AttLayer where
  clears : List (Int × Int × Int)
  entries : List AttEntry
deriving Inhabited

def AttLayer.A (L : AttLayer) : List (Nat × Int) := L.entries.map fun e => (e.s, e.a)

structure Ply where
  FR : Array Int
  TO : Array Int
  MP : List Int
  RT : List Int
  CAP : Int
  PROMO : Int
  FRL : List Int
  TOL : List Int
  EPR : List (Nat × Int)
  CH : List Int
deriving Inhabited

structure Layout where
  X : Array (Array (List Int))
  XL : Array (Array (List Int))
  AT : Array (Array AttLayer)
  EPS : Array (List (Nat × Int))
  PL : Array Ply
  L0 : List Int
  LS : Array (List Int)
  S : Array (List Int)

def look (l : List (Nat × Int)) (s : Nat) : Option Int := (l.find? (·.1 == s)).map (·.2)

def xv (X : Array (List Int)) (s k : Nat) : Int := (X.getD s []).getD k 0

def boardAlloc (g : Cfg) (t : Nat) : AM (Array (List Int) × Array (List Int)) := do
  let mut X : Array (List Int) := Array.replicate 64 []
  let mut XL : Array (List Int) := Array.replicate 64 []
  for s in g.NK do
    let rs := (List.range 11).map fun k => Sem.x t s k
    let xs ← freshMany (rs.map .sem)
    let lad ← amoAlloc rs
    X := X.set! s xs
    XL := XL.set! s lad
  return (X, XL)

def boardCls (g : Cfg) (X XL : Array (List Int)) : List Clause :=
  g.NK.flatMap fun s => X.getD s [] :: amoCls (X.getD s []) (XL.getD s [])

inductive ALit where
  | x (s k : Nat)
  | clr (ss : List Nat)
deriving Repr, Inhabited, DecidableEq

def ALit.sem (t : Nat) : ALit → Sem
  | .x s k => .x t s k
  | .clr ss => .clear t ss

def insertAlt (al : List (Nat × List (List ALit))) (s : Nat) (c : List ALit) : List (Nat × List (List ALit)) :=
  if al.any (·.1 == s) then al.map fun e => if e.1 == s then (e.1, e.2 ++ [c]) else e
  else al ++ [(s, [c])]

def clearLit (ray : List Nat) (j : Nat) : Option ALit :=
  if j = 0 then none else if j = 1 then some (.x (ray.getD 0 0) EMP) else some (.clr (ray.take j))

def attAlts (g : Cfg) (x : Nat) : List (Nat × List (List ALit)) :=
  let y := 1 - x
  let k := g.K x
  let base := g.NK.foldl (fun al s =>
    let al := if attacksGeom N y s k then insertAlt al s [.x s (5 * y + N)] else al
    if attacksGeom P y s k then insertAlt al s [.x s (5 * y + P)] else al) []
  (orth ++ diag).foldl (fun al d =>
    let sl := if orth.contains d then R else B
    let ray := g.ray x d
    (List.range ray.length).foldl (fun al j =>
      [Q, sl].foldl (fun al p =>
        insertAlt al (ray.getD j 0) ((clearLit ray j).toList ++ [.x (ray.getD j 0) (5 * y + p)])) al) al) base

def attClears (g : Cfg) (x : Nat) : List (List Nat) :=
  (orth ++ diag).flatMap fun d =>
    let ray := g.ray x d
    ((List.range ray.length).filter (2 ≤ ·)).map ray.take

def attAlloc (g : Cfg) (t x : Nat) (X : Array (List Int)) : AM AttLayer := do
  let cl ← (attClears g x).mapM fun ss => do return (ss, ← fresh (.sem (.clear t ss)))
  let lid : ALit → Int := fun
    | .x s k => xv X s k
    | .clr ss => ((cl.find? (·.1 == ss)).map (·.2)).getD 0
  let clears := cl.map fun (ss, c) =>
    (c, lid ((clearLit ss (ss.length - 1)).getD (.x 0 0)), xv X (ss.getD (ss.length - 1) 0) EMP)
  let entries ← (attAlts g x).mapM fun (s, conjs) => do
    let a ← fresh (.sem (.att t x s))
    let cs ← conjs.mapM fun conj =>
      if conj.length = 1 then pure (conj.map lid, none)
      else do return (conj.map lid, some (← fresh (.conj (conj.map (ALit.sem t)))))
    return ({ s, a, conjs := cs } : AttEntry)
  return { clears, entries }

def attCls (L : AttLayer) : List (Clause × Fam) :=
  (L.clears.flatMap fun (c, pv, e) => tag .clear [[-c, pv], [-c, e], [c, -pv, -e]]) ++
  L.entries.flatMap fun en =>
    (en.conjs.flatMap fun (lits, aux) =>
      tag .attack ((lits.map Neg.neg ++ [en.a]) ::
        match aux with
        | none => []
        | some v => lits.map (fun l => [-v, l]) ++ [lits.map Neg.neg ++ [v]])) ++
    tag .attack [-en.a :: en.conjs.map fun (lits, aux) => aux.getD (lits.getD 0 0)]

def epSquares (g : Cfg) (t : Nat) : List Nat :=
  let c := g.col t
  let trank : Int := if c = 0 then 5 else 2
  g.NK.filter fun s =>
    rk s == trank && !g.isK (sqOf (fl s) (rk s - pdir c)) && !g.isK (sqOf (fl s) (rk s + pdir c))

def epAlloc (g : Cfg) (t : Nat) : AM (List (Nat × Int)) :=
  (epSquares g t).mapM fun s => do return (s, ← fresh (.sem (.eps t s)))

def epCls (g : Cfg) (t : Nat) (X0 : Array (List Int)) (pl : Option Ply) (E : List (Nat × Int)) :
    List (Clause × Fam) :=
  let c := g.col t
  let e := 1 - c
  (E.flatMap fun (s, v) =>
    let dsq := sqOf (fl s) (rk s - pdir c)
    let osq := sqOf (fl s) (rk s + pdir c)
    match pl with
    | none => tag .ep [[-v, xv X0 dsq (5 * e + P)], [-v, xv X0 s EMP], [-v, xv X0 osq EMP]]
    | some q =>
      let fr := q.FR.getD osq 0
      let to := q.TO.getD dsq 0
      let mp := q.MP.getD P 0
      tag .ep [[-v, fr], [-v, to], [-v, mp], [-fr, -to, -mp, v]]) ++
  (if pl.isNone then tag .ep (amoCls (E.map (·.2)) []) else [])

def eprSquares (g : Cfg) (t : Nat) (E : List (Nat × Int)) : List (Nat × Nat × List Nat) :=
  let c := g.col t
  let rr : Int := if c = 0 then 4 else 3
  g.NK.filterMap fun r =>
    if rk r != rr then none else
      let gq := sqOf (fl r) (rk r + pdir c)
      if (look E gq).isNone then none else
        let srcs := [-1, 1].filterMap fun df =>
          if onb (fl r + df) (rk r) && !g.isK (sqOf (fl r + df) (rk r)) then some (sqOf (fl r + df) (rk r)) else none
        if srcs.isEmpty then none else some (r, gq, srcs)

def toArr (l : List (Nat × Int)) : Array Int :=
  l.foldl (fun a (s, v) => a.set! s v) (Array.replicate 64 0)

def plyAlloc (g : Cfg) (t : Nat) (E : List (Nat × Int)) : AM Ply := do
  let fr ← g.NK.mapM fun s => do return (s, ← fresh (.sem (.fr t s)))
  let to ← g.NK.mapM fun s => do return (s, ← fresh (.sem (.to t s)))
  let mp ← freshMany ((List.range 5).map fun p => .sem (.mp t p))
  let rt ← freshMany ((List.range 5).map fun p => .sem (.rt t p))
  let cap ← fresh (.sem (.cap t))
  let promo ← fresh (.sem (.promo t))
  let frl ← amoAlloc (g.NK.map (Sem.fr t))
  let tol ← amoAlloc (g.NK.map (Sem.to t))
  let epr ← (eprSquares g t E).mapM fun (r, _, _) => do return (r, ← fresh (.sem (.epr t r)))
  let ch ← g.NK.mapM fun s => fresh (.sem (.ch t s))
  return { FR := toArr fr, TO := toArr to, MP := mp, RT := rt, CAP := cap, PROMO := promo,
           FRL := frl, TOL := tol, EPR := epr, CH := ch }

def Ply.fr (q : Ply) (s : Nat) : Int := q.FR.getD s 0

def Ply.to (q : Ply) (s : Nat) : Int := q.TO.getD s 0

def Ply.mp (q : Ply) (p : Nat) : Int := q.MP.getD p 0

def Ply.rt (q : Ply) (p : Nat) : Int := q.RT.getD p 0

def plyMove1Cls (g : Cfg) (q : Ply) : List (Clause × Fam) :=
  let frs := g.NK.map q.fr
  let tos := g.NK.map q.to
  tag .move1 (frs :: amoCls frs q.FRL) ++ tag .move1 (tos :: amoCls tos q.TOL) ++
    tag .move1 (q.MP :: amoCls q.MP []) ++ tag .move1 (q.RT :: amoCls q.RT [])

def plyEprCls (g : Cfg) (t : Nat) (X0 X1 : Array (List Int)) (E : List (Nat × Int)) (q : Ply) :
    List (Clause × Fam) :=
  let e := 1 - g.col t
  (eprSquares g t E).flatMap fun (r, gq, srcs) =>
    match look q.EPR r with
    | none => []
    | some v =>
      tag .ep [[-v, q.to gq], [-v, q.mp P], [-v, xv X0 r (5 * e + P)], [-v, (look E gq).getD 0],
        [-v, xv X0 gq EMP], -v :: srcs.map q.fr, [-v, xv X1 r EMP]]

def plySqCls (g : Cfg) (t : Nat) (X0 : Array (List Int)) (q : Ply) : List (Clause × Fam) :=
  let c := g.col t
  let p5 := List.range 5
  g.NK.flatMap fun s =>
    tag .move1 [[-q.fr s, -q.to s]] ++
    tag .source ((-q.fr s :: p5.map fun p => xv X0 s (5 * c + p)) ::
      p5.flatMap fun p => [[-q.fr s, -q.mp p, xv X0 s (5 * c + p)], [-q.fr s, -xv X0 s (5 * c + p), q.mp p]]) ++
    tag .dest (p5.map fun p => [-q.to s, -xv X0 s (5 * c + p)])

def plyPairCls (g : Cfg) (t : Nat) (X0 : Array (List Int)) (q : Ply) (f h : Nat) : List (Clause × Fam) :=
  let c := g.col t
  let ts := g.allowed c f h
  if ts.isEmpty then tag .geom [[-q.fr f, -q.to h]] else
    (if ts.length < 5 then tag .geom [[-q.fr f, -q.to h] ++ ts.map q.mp] else []) ++
    tag .transit ((btw f h).map fun s => [-q.fr f, -q.to h, xv X0 s EMP]) ++
    (if ts.contains P then
      if fl f = fl h then tag .pawn [[-q.fr f, -q.to h, -q.mp P, xv X0 h EMP]]
      else
        let r := sqOf (fl h) (rk h - pdir c)
        match look q.EPR r with
        | some v => tag .pawn [[-q.fr f, -q.to h, -q.mp P, -xv X0 h EMP, v]]
        | none => tag .pawn [[-q.fr f, -q.to h, -q.mp P, -xv X0 h EMP]]
    else [])

def plyGeomCls (g : Cfg) (t : Nat) (X0 : Array (List Int)) (q : Ply) : List (Clause × Fam) :=
  g.NK.flatMap fun f => g.NK.flatMap fun h => if f = h then [] else plyPairCls g t X0 q f h

def plyCapCls (g : Cfg) (X0 : Array (List Int)) (q : Ply) : List (Clause × Fam) :=
  let epl := q.EPR.map (·.2)
  (g.NK.flatMap fun h => tag .cap [[-q.to h, xv X0 h EMP, q.CAP], [-q.CAP, -q.to h, -xv X0 h EMP] ++ epl]) ++
    tag .cap (epl.map fun v => [-v, q.CAP])

def plyPromoCls (g : Cfg) (t : Nat) (q : Ply) : List (Clause × Fam) :=
  let last : Int := if g.col t = 0 then 7 else 0
  let lt := (g.NK.filter fun h => rk h == last).map q.to
  tag .promo ([[-q.PROMO, q.mp P], -q.PROMO :: lt] ++ lt.map (fun l => [-q.mp P, -l, q.PROMO]) ++
    (List.range 5).flatMap (fun p => [[q.PROMO, -q.mp p, q.rt p], [q.PROMO, -q.rt p, q.mp p]]) ++
    [[-q.PROMO, -q.rt P]])

def plyFrameCls (g : Cfg) (t : Nat) (X0 X1 : Array (List Int)) (q : Ply) : List (Clause × Fam) :=
  let c := g.col t
  (g.NK.zip q.CH).flatMap fun (s, ch) =>
    let lits := [q.fr s, q.to s] ++ (look q.EPR s).toList
    tag .update ([-q.fr s, xv X1 s EMP] :: (List.range 5).map fun p => [-q.to s, -q.rt p, xv X1 s (5 * c + p)]) ++
    tag .frame ((-ch :: lits) :: lits.map (fun l => [-l, ch]) ++
      (List.range 11).flatMap fun k => [[ch, -xv X0 s k, xv X1 s k], [ch, xv X0 s k, -xv X1 s k]])

def plyCls (g : Cfg) (t : Nat) (X0 X1 : Array (List Int)) (E : List (Nat × Int)) (q : Ply) :
    List (Clause × Fam) :=
  plyMove1Cls g q ++ plyEprCls g t X0 X1 E q ++ plySqCls g t X0 q ++ plyGeomCls g t X0 q ++
    plyCapCls g X0 q ++ plyPromoCls g t q ++ plyFrameCls g t X0 X1 q

def counterAlloc (g : Cfg) (caps : List Int) : AM (List (List Int)) :=
  if g.m = 0 then pure []
  else (List.range caps.length).mapM fun i =>
    freshMany ((List.range (g.m + 1)).map fun j => .count ((List.range g.n).map Sem.cap) i j)

def counterCls (g : Cfg) (caps : List Int) (S : List (List Int)) : List Clause :=
  if g.m = 0 then caps.map fun c => [-c]
  else
    let k := g.m + 1
    ((List.range caps.length).flatMap fun i =>
      let x := caps.getD i 0
      let row := S.getD i []
      (List.range k).flatMap fun j =>
        let pj : Option Int := if i > 0 then some ((S.getD (i - 1) []).getD j 0) else none
        let pjm : Option (Option Int) :=
          if j > 0 then (if i > 0 then some (some ((S.getD (i - 1) []).getD (j - 1) 0)) else none)
          else some none
        let rj := row.getD j 0
        let cl := -rj :: pj.toList
        (match pj with | some v => [[-v, rj]] | none => []) ++
        (match pjm with
          | some none => [[-x, rj]]
          | some (some v) => [[-x, -v, rj]]
          | none => []) ++
        (match pjm with
          | some none => [cl ++ [x]]
          | some (some v) => [cl ++ [x], cl ++ [v]]
          | none => [cl])) ++
    [[-((S.getD (caps.length - 1) []).getD g.m 0)]]

def Layout.X0 (Ly : Layout) (t : Nat) : Array (List Int) := Ly.X.getD t #[]

def Layout.att (Ly : Layout) (t x : Nat) : AttLayer := (Ly.AT.getD t #[]).getD x default

def Layout.ply (Ly : Layout) (t : Nat) : Ply := Ly.PL.getD t default

def r1Cls (g : Cfg) (Ly : Layout) (t : Nat) : List Clause :=
  let e := 1 - g.col t
  let q := Ly.ply t
  (Ly.att (t + 1) e).A.map fun (qs, a) =>
    let bt := btw qs (g.K e)
    [-a, q.to qs] ++ bt.map q.fr ++ (bt.filterMap fun s => look q.EPR s)

def discLits (g : Cfg) (Ly : Layout) (t : Nat) : List Int :=
  let rse := g.raySquares (1 - g.col t)
  let q := Ly.ply t
  (g.NK.filter rse.contains).map q.fr ++ (q.EPR.filter fun (r, _) => rse.contains r).map (·.2)

def r4Cls (g : Cfg) (Ly : Layout) (t : Nat) : List Clause :=
  let c := g.col t
  let ke := g.K (1 - c)
  let q := Ly.ply t
  g.NK.flatMap fun h => (List.range 5).filterMap fun p =>
    if !attacksGeom p c h ke || (btw h ke).any g.isK then some ([-q.to h, -q.rt p] ++ discLits g Ly t) else none

def r2Cls (g : Cfg) (Ly : Layout) (t : Nat) : List Clause :=
  let c := g.col t
  let q := Ly.ply t
  (Ly.att t c).A.map fun (qs, a) => [-a, q.to qs] ++ (look q.EPR qs).toList ++ (btw qs (g.K c)).map q.to

def r3Cls (g : Cfg) (Ly : Layout) (t : Nat) : List Clause :=
  let c := g.col t
  let q := Ly.ply t
  if t ≥ 1 then
    g.NK.filterMap fun h =>
      if g.cand c h then none else
        let r := sqOf (fl h) (rk h - pdir c)
        match look q.EPR r with
        | some v => if g.cand c r then some [-q.to h, v] else some [-q.to h]
        | none => some [-q.to h]
  else []

def redundantCls (g : Cfg) (Ly : Layout) : List (Clause × Fam) :=
  (List.range g.n).flatMap fun t =>
    tag .r1 (r1Cls g Ly t) ++ tag .r4 (r4Cls g Ly t) ++ tag .r2 (r2Cls g Ly t) ++ tag .r3 (r3Cls g Ly t)

def layoutM (g : Cfg) : AM Layout := do
  let mut X : Array (Array (List Int)) := #[]
  let mut XL : Array (Array (List Int)) := #[]
  for t in List.range (g.n + 1) do
    let (a, b) ← boardAlloc g t
    X := X.push a
    XL := XL.push b
  let mut AT : Array (Array AttLayer) := #[]
  for t in List.range (g.n + 1) do
    let l0 ← attAlloc g t 0 (X.getD t #[])
    let l1 ← attAlloc g t 1 (X.getD t #[])
    AT := AT.push #[l0, l1]
  let mut EPS : Array (List (Nat × Int)) := #[← epAlloc g 0]
  let mut PL : Array Ply := #[]
  for t in List.range g.n do
    let q ← plyAlloc g t (EPS.getD t [])
    PL := PL.push q
    EPS := EPS.push (← epAlloc g (t + 1))
  let attRoles := fun t x => (((AT.getD t #[]).getD x default).A).map fun (s, _) => Sem.att t x s
  let L0 ← if g.n ≥ 1 then amoAlloc (attRoles 0 0) else pure []
  let mut LS : Array (List Int) := #[]
  for t in List.range g.n do
    let e := 1 - g.col t
    if t + 1 ≤ g.n - 1 then LS := LS.push (← amoAlloc (attRoles (t + 1) e))
    else LS := LS.push []
  let S ← counterAlloc g (PL.toList.map (·.CAP))
  return { X, XL, AT, EPS, PL, L0, LS, S := S.toArray }

def boardPart (g : Cfg) (Ly : Layout) : List (Clause × Fam) :=
  (List.range (g.n + 1)).flatMap fun t => tag .onehot (boardCls g (Ly.X0 t) (Ly.XL.getD t #[]))

def attPart (g : Cfg) (Ly : Layout) : List (Clause × Fam) :=
  (List.range (g.n + 1)).flatMap fun t => attCls (Ly.att t 0) ++ attCls (Ly.att t 1)

def ep0Part (g : Cfg) (Ly : Layout) : List (Clause × Fam) := epCls g 0 (Ly.X0 0) none (Ly.EPS.getD 0 [])

def pliesPart (g : Cfg) (Ly : Layout) : List (Clause × Fam) :=
  (List.range g.n).flatMap fun t =>
    plyCls g t (Ly.X0 t) (Ly.X0 (t + 1)) (Ly.EPS.getD t []) (Ly.ply t) ++
      epCls g (t + 1) (Ly.X0 (t + 1)) (some (Ly.ply t)) (Ly.EPS.getD (t + 1) [])

def startPart (g : Cfg) (Ly : Layout) : List (Clause × Fam) :=
  tag .start ((g.NK.filter fun s => rk s == 0 || rk s == 7).flatMap fun s =>
      [[-xv (Ly.X0 0) s P], [-xv (Ly.X0 0) s (5 + P)]]) ++
    tag .start ((Ly.att 0 1).A.map fun (_, a) => [-a])

def chk0Part (g : Cfg) (Ly : Layout) : List (Clause × Fam) :=
  if g.n ≥ 1 then tag .check (amoCls ((Ly.att 0 0).A.map (·.2)) Ly.L0) else []

def perPart (g : Cfg) (Ly : Layout) : List (Clause × Fam) :=
  (List.range g.n).flatMap fun t =>
    let c := g.col t
    let e := 1 - c
    tag .legal ((Ly.att (t + 1) c).A.map fun (_, a) => [-a]) ++
    tag .check [(Ly.att (t + 1) e).A.map (·.2)] ++
    (if t + 1 ≤ g.n - 1 then tag .check (amoCls ((Ly.att (t + 1) e).A.map (·.2)) (Ly.LS.getD t [])) else [])

def capsPart (g : Cfg) (Ly : Layout) : List (Clause × Fam) :=
  tag .capcount (counterCls g (Ly.PL.toList.map (·.CAP)) Ly.S.toList)

def clausesOf (g : Cfg) (Ly : Layout) : List (Clause × Fam) :=
  boardPart g Ly ++ attPart g Ly ++ ep0Part g Ly ++ pliesPart g Ly ++ startPart g Ly ++ chk0Part g Ly ++
    perPart g Ly ++ capsPart g Ly ++ redundantCls g Ly

structure Encoding where
  cfg : Cfg
  layout : Layout
  alloc : Alloc
  cls : List (Clause × Fam)

def encodeCfg (g : Cfg) : Encoding :=
  let (Ly, a) := (layoutM g).run { nv := 0, roles := #[] }
  { cfg := g, layout := Ly, alloc := a, cls := clausesOf g Ly }

def Encoding.formula (E : Encoding) : Formula := { nv := E.alloc.nv, clauses := E.cls.map (·.1) }

def encode (w b : Sq) (n m : Nat) : Encoding := encodeCfg { kw := w.val, kb := b.val, n, m }

def F (w b : Sq) (n m : Nat) : Formula := (encode w b n m).formula

end Chess.C364.Enc
