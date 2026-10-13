import ChessProof.Spec

namespace Chess

def AllCheckLe63 : Prop :=
  ∀ p : Pos, Reachable p → (∀ m ∈ legalMoves p, givesCheck p m = true) → (legalMoves p).length ≤ 63

def AllCheck63Attained : Prop :=
  ∃ p : Pos, Reachable p ∧ (∀ m ∈ legalMoves p, givesCheck p m = true) ∧ (legalMoves p).length = 63

def ChecksLe364 : Prop :=
  ∀ (p : Pos) (ms : List Move), Reachable p → IsCheckSeq p ms → ms.length ≤ 364

end Chess
