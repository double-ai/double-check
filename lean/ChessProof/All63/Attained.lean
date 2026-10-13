import ChessProof.Spec

namespace Chess.All63

def promoOf : Char → Kind
  | 'n' => .knight
  | 'b' => .bishop
  | 'r' => .rook
  | _ => .queen

def uci (s : String) : Move :=
  match s.toList with
  | [a, b, c, d] => ⟨sq (a.toNat - 97) (b.toNat - 49), sq (c.toNat - 97) (d.toNat - 49), none⟩
  | [a, b, c, d, e] => ⟨sq (a.toNat - 97) (b.toNat - 49), sq (c.toNat - 97) (d.toNat - 49), some (promoOf e)⟩
  | _ => default

def game63 : List Move := List.map uci [
    "a2a3", "b7b5", "c2c4", "b5b4", "a3b4", "d7d5", "c4d5", "h7h5", "g2g4", "e7e5",
    "g4h5", "f7f5", "g1f3", "c7c5", "f3e5", "c5c4", "e5f3", "g7g5", "f3d4", "c4c3",
    "d4f5", "g5g4", "d2d3", "c3c2", "c1d2", "g4g3", "d2c3", "g3g2", "e2e4", "g2g1q",
    "b1d2", "g1g4", "f1e2", "c2c1q", "b4b5", "e8d7", "h2h4", "a7a5", "d5d6", "g4g5",
    "b5b6", "a5a4", "h5h6", "g5g4", "b2b4", "d8f6", "b6b7", "f8e7", "e4e5", "a8a5",
    "e5e6", "d7c6", "d6d7", "a5a7", "d3d4", "f6g5", "h4h5", "g4g3", "h6h7", "c6b6",
    "h5h6", "g3h4", "d4d5", "h4h2", "d5d6", "c1a3", "a1c1", "b8c6", "d2e4", "e7f8",
    "e6e7", "a3b2", "c3d2", "c6a5", "c1c2", "g5g4", "e2f3", "b2b1", "e1e2", "a5c6",
    "e4c3", "b1b3", "h1g1", "g4d4", "f3h1", "g8f6", "g1g2", "f6e8", "d1g1", "c6a5",
    "b7b8q", "c8b7", "f5g3", "d4g4", "e2d3", "b3b1", "d2f4", "a5b3", "f4g5", "h8g8",
    "h7h8q", "a7a6", "h6h7", "f8h6", "h8e5", "g4d1", "g5d2", "g8g4", "f2f3", "h6e3",
    "f3f4", "h2h5", "g1f2", "g4h4", "f2g1", "h4h3", "g1f2", "a6a7", "f2g1", "b6a6",
    "g1f2", "b7d5", "f2g1", "a7b7", "g1f2", "a6b6", "f2g1", "d5e6", "e5a5", "b6c6",
    "h7h8q", "b7b6", "h8e5", "e6g8", "g3f5", "h5h7", "g1f2", "b6b7", "f2g1", "b7c7",
    "g1f2", "c7c8", "f2g1", "e8g7", "g1f2", "c8f8", "f2g1", "d1h5", "d2c1", "g7e8",
    "b8a7", "h3h4", "a7b8", "e3d2", "g1a7", "d2e3", "c1d2", "h4h3", "d2c1", "f8f6",
    "c1d2", "b3d4", "d2c1", "d4f3", "c1d2", "e3f2", "d2c1", "f2e1", "c1e3", "h5g4",
    "d7d8q", "e1d2", "d6d7", "e8g7", "d8e8", "d2c1", "e8f7", "c1a3", "d7d8q", "g7e8",
    "e5d4", "f3d2", "f7e6", "e8d6", "e6e5", "d6e8", "g2f2", "g4f3", "f2g2", "f3d1"]

def norm (p : Pos) : Pos :=
  let a := Array.ofFn p.board
  { p with board := fun s => a.getD s.val none }

theorem norm_eq (p : Pos) : norm p = p := by
  cases p
  simp only [norm, Pos.mk.injEq, and_true]
  funext s
  simp [Array.getD_eq_getD_getElem?, s.isLt]

def runLine : Pos → List Move → Option Pos
  | p, [] => some p
  | p, m :: ms => if m ∈ legalMoves p then runLine (norm (play p m)) ms else none

theorem reachable_runLine {p q : Pos} {ms : List Move} (hp : Reachable p) (h : runLine p ms = some q) :
    Reachable q := by
  induction ms generalizing p with
  | nil => simp only [runLine, Option.some.injEq] at h; exact h ▸ hp
  | cons m ms ih =>
    simp only [runLine] at h
    split at h
    · exact ih (norm_eq _ ▸ Reachable.step hp ‹_›) h
    · cases h

def okAt (o : Option Pos) : Bool :=
  match o with
  | some q => (legalMoves q).length == 63 && (legalMoves q).all (givesCheck q)
  | none => false

theorem of_okAt {o : Option Pos} (h : okAt o = true) :
    ∃ q, o = some q ∧ (∀ m ∈ legalMoves q, givesCheck q m = true) ∧ (legalMoves q).length = 63 := by
  cases o with
  | none => cases h
  | some q =>
    simp only [okAt, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    exact ⟨q, rfl, h.2, h.1⟩

theorem ok63 : okAt (runLine initial game63) = true := by native_decide

theorem attained63 : ∃ p : Pos, Reachable p ∧ (∀ m ∈ legalMoves p, givesCheck p m = true) ∧
    (legalMoves p).length = 63 := by
  obtain ⟨q, hq, hc, hl⟩ := of_okAt ok63
  exact ⟨q, reachable_runLine Reachable.init hq, hc, hl⟩

end Chess.All63
