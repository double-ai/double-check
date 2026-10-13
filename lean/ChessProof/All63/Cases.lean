import ChessProof.All63.Enc

namespace Chess.All63

def cases : List Cfg :=
  [false, true].flatMap fun ck => (List.range 64).flatMap fun kw =>
    (List.range 64).filterMap fun kb => if 1 < cheb kw kb then some ⟨kw, kb, ck⟩ else none

def caseAt (i : Nat) : Cfg := cases.getD i default

theorem cases_length : cases.length = 7224 := by decide +kernel

theorem mem_cases (c : Cfg) (h1 : c.kw < 64) (h2 : c.kb < 64) (h3 : 1 < cheb c.kw c.kb) : c ∈ cases := by
  obtain ⟨kw, kb, ck⟩ := c
  simp only [cases, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  refine ⟨ck, by cases ck <;> simp, kw, h1, kb, h2, ?_⟩
  simp_all

theorem exists_caseAt (c : Cfg) (h : c ∈ cases) : ∃ i, i < 7224 ∧ caseAt i = c := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  refine ⟨i, cases_length ▸ hi, ?_⟩
  simp only [caseAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he]

end Chess.All63
