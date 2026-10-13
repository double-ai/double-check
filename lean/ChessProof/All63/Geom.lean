import ChessProof.Spec

namespace Chess.All63

def fr (s : Nat) : Int × Int := ((s % 8 : Nat), (s / 8 : Nat))

def sqo (f r : Int) : Option Nat :=
  if 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8 then some (f + 8 * r).toNat else none

def orth : List (Int × Int) := [(1, 0), (-1, 0), (0, 1), (0, -1)]

def diag : List (Int × Int) := [(1, 1), (1, -1), (-1, 1), (-1, -1)]

def kn : List (Int × Int) := [(1, 2), (2, 1), (-1, 2), (-2, 1), (1, -2), (2, -1), (-1, -2), (-2, -1)]

def rayGo (d : Int × Int) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, s =>
    match sqo ((fr s).1 + d.1) ((fr s).2 + d.2) with
    | none => []
    | some x => x :: rayGo d n x

def rayL (s : Nat) (d : Int × Int) : List Nat := rayGo d 8 s

def sgn (x : Int) : Int := if 0 < x then 1 else if x < 0 then -1 else 0

def direction (a b : Nat) : Option (Int × Int) :=
  let df := (fr b).1 - (fr a).1
  let dr := (fr b).2 - (fr a).2
  if ((df == 0) == (dr == 0)) && df.natAbs != dr.natAbs then none
  else if df == 0 && dr == 0 then none
  else some (sgn df, sgn dr)

def between (a b : Nat) : List Nat :=
  match direction a b with
  | none => []
  | some d =>
    let r := rayL a d
    if r.contains b then r.takeWhile (· != b) else []

def cheb (a b : Nat) : Nat :=
  max ((fr a).1 - (fr b).1).natAbs ((fr a).2 - (fr b).2).natAbs

def knightL (s : Nat) : List Nat :=
  kn.filterMap fun d => sqo ((fr s).1 + d.1) ((fr s).2 + d.2)

def toSq (n : Nat) : Sq := ⟨n % 64, Nat.mod_lt _ (by decide)⟩

end Chess.All63
