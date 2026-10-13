import ChessProof.Spec
import ChessProof.C364.Geom

namespace Chess.C364

open Chess

def isSlider (k : Kind) : Bool := k == .bishop || k == .rook || k == .queen

def geomAttack (c : Color) (k : Kind) (s t : Sq) : Bool :=
  match k with
  | .pawn => ry t == ry s + c.fwd && (fx t - fx s).natAbs == 1
  | .knight => knightJump s t
  | .king => kdist s t == 1
  | .bishop => diagLine s t
  | .rook => orthLine s t
  | .queen => aligned s t

def clearPath (b : Board) (s t : Sq) : Prop := ∀ z, inSeg s t z = true → b z = none

def kingAt (p : Pos) (c : Color) (s : Sq) : Prop := p.board s = some ⟨c, .king⟩

def isKingMove (p : Pos) (m : Move) : Bool := (p.board m.src).any (·.kind == .king)

def isCastle (p : Pos) (m : Move) : Bool :=
  isKingMove p m && (m.src.file + 2 == m.dst.file || m.dst.file + 2 == m.src.file)

def epVictim (p : Pos) (m : Move) : Option Sq :=
  if (p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file && empty p.board m.dst then
    some (sq m.dst.file m.src.rank)
  else none

def isCapture (p : Pos) (m : Move) : Bool := (p.board m.dst).isSome || (epVictim p m).isSome

def checkers (p : Pos) (k : Sq) : List Sq :=
  allSq.filter fun t =>
    match p.board t with
    | some q => q.color == p.turn.opp && (attacks p.board t q).contains k
    | none => false

def nonKing (p : Pos) : Nat :=
  (allSq.filter fun s => (p.board s).any (·.kind != .king)).length

def after (p : Pos) (ms : List Move) : Pos := ms.foldl play p

def KFChain : Pos → List Move → Prop
  | _, [] => True
  | p, m :: ms => m ∈ legalMoves p ∧ givesCheck p m = true ∧ isKingMove p m = false ∧ KFChain (play p m) ms

def caps : Pos → List Move → Nat
  | _, [] => 0
  | p, m :: ms => (if isCapture p m then 1 else 0) + caps (play p m) ms

def kingPlies : Pos → List Move → Nat
  | _, [] => 0
  | p, m :: ms => (if isKingMove p m then 1 else 0) + kingPlies (play p m) ms

def epOk (p : Pos) (t : Sq) : Prop :=
  ry t = (if p.turn = .white then 5 else 2) ∧ p.board t = none ∧
    (∃ o, off t 0 p.turn.fwd = some o ∧ p.board o = none) ∧
    (∃ d, off t 0 (-p.turn.fwd) = some d ∧ p.board d = some ⟨p.turn.opp, .pawn⟩)

structure C0 (p : Pos) : Prop where
  wk : ∃ w, ∀ s, p.board s = some ⟨.white, .king⟩ ↔ s = w
  bk : ∃ b, ∀ s, p.board s = some ⟨.black, .king⟩ ↔ s = b
  apart : ∀ w b, p.board w = some ⟨.white, .king⟩ → p.board b = some ⟨.black, .king⟩ → 2 ≤ kdist w b
  pawns : ∀ s c, p.board s = some ⟨c, .pawn⟩ → ry s ≠ 0 ∧ ry s ≠ 7
  safe : inCheck p p.turn.opp = false
  ep : ∀ t, p.ep = some t → epOk p t

def BoundB (k L : Nat) : Prop :=
  ∀ p ms, C0 p → KFChain p ms → caps p ms ≤ k → ms.length ≤ L

def ChainAt (w b : Sq) (n m : Nat) (p : Pos) (ms : List Move) : Prop :=
  C0 p ∧ p.turn = .white ∧ kingAt p .white w ∧ kingAt p .black b ∧ KFChain p ms ∧ ms.length = n ∧
    caps p ms ≤ m

def NoChain (w b : Sq) (n m : Nat) : Prop := ∀ p ms, ¬ ChainAt w b n m p ms

def f (C : Nat) : Nat := 23 * (C / 2) + if C % 2 = 0 then 19 else 22

end Chess.C364
