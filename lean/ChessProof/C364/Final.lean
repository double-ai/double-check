import ChessProof.C364.Certificate
import ChessProof.C364.Axioms

namespace Chess.C364

theorem checks_le_364_final : ∀ (p : Pos) (ms : List Move), Reachable p → IsCheckSeq p ms → ms.length ≤ 364 :=
  checks_le_364_of_facts routeB364_facts

end Chess.C364
