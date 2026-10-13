import ChessProof.All63.Main
import ChessProof.All63.Axioms
import ChessProof.All63.Attained

namespace Chess.All63

theorem allcheck_le_63_final : ∀ p : Pos, Reachable p → (∀ m ∈ legalMoves p, givesCheck p m = true) →
    (legalMoves p).length ≤ 63 :=
  allcheck_le_63_of routeB_facts

theorem allcheck_63_attained_final : ∃ p : Pos, Reachable p ∧ (∀ m ∈ legalMoves p, givesCheck p m = true) ∧
    (legalMoves p).length = 63 :=
  attained63

end Chess.All63
