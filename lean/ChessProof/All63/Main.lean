import ChessProof.All63.Sound
import ChessProof.All63.Trust

namespace Chess.All63

theorem cfgOf_fits {p : Pos} (hA : Admissible p) (hw : p.turn = .white) : Fits (cfgOf p) p := ⟨hA, hw, rfl⟩

theorem cfgOf_mem {p : Pos} (hA : Admissible p) (hw : p.turn = .white) : cfgOf p ∈ cases := by
  obtain ⟨h1, h2, h3⟩ := fits_cfgOk (cfgOf_fits hA hw)
  exact mem_cases _ h1 h2 h3

theorem le63_white (U : UnsatFacts) (p : Pos) (hA : Admissible p) (hw : p.turn = .white) (hall : AllCheck p) :
    (legalMoves p).length ≤ 63 := by
  apply Nat.le_of_not_lt
  intro hlt
  obtain ⟨i, hi, hc⟩ := exists_caseAt _ (cfgOf_mem hA hw)
  have hu := U.unsat i hi
  simp only [G63, hc] at hu
  exact hu _ (encode_sat (cfgOf_fits hA hw) hall hlt)

theorem le63_admissible (U : UnsatFacts) (p : Pos) (hA : Admissible p) (hall : AllCheck p) :
    (legalMoves p).length ≤ 63 :=
  reduce_white (fun q => Admissible q ∧ AllCheck q)
    (fun q hq => ⟨admissible_flip q hq.1, allCheck_flip q hq.2⟩)
    (fun q hq hw => le63_white U q hq.1 hw hq.2) p ⟨hA, hall⟩

theorem allcheck_le_63_of (U : UnsatFacts) (p : Pos) (hp : Reachable p)
    (hall : ∀ m ∈ legalMoves p, givesCheck p m = true) : (legalMoves p).length ≤ 63 :=
  le63_admissible U p (reachable_admissible hp) hall

end Chess.All63
