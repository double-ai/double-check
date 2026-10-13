import ChessProof.Trust
import ChessProof.C364.CertData

namespace Chess.C364

open Chess.C364.Fm Chess.C364.Enc Chess.C364.Tree

def Fm.Formula.toCnf (F : Formula) : Chess.Cnf := ⟨F.nv, (F.clauses.map List.toArray).toArray⟩

theorem Fm.Formula.sat_toCnf (F : Formula) (σ : Assign) (h : F.eval σ = true) : F.toCnf.Sat σ := by
  intro c hc
  simp only [Formula.toCnf, List.mem_toArray, List.mem_map] at hc
  obtain ⟨l, hl, rfl⟩ := hc
  simp only [Formula.eval, List.all_eq_true] at h
  have h1 := h l hl
  simp only [Clause.eval, List.any_eq_true] at h1
  obtain ⟨x, hx, he⟩ := h1
  simp only [Chess.Clause.sat, List.any_toArray, List.any_eq_true]
  exact ⟨x, hx, he⟩

theorem Fm.Formula.unsat_of_toCnf (F : Formula) (h : F.toCnf.Unsat) : Unsat F :=
  fun ⟨σ, hσ⟩ => h σ (F.sat_toCnf σ hσ)

structure Record where
  kw : Sq
  kb : Sq
  n : Nat
  m : Nat
  extra : List Fm.Clause
deriving Inhabited

def Record.formula (r : Record) : Formula := (F r.kw r.kb r.n r.m).add r.extra

def treeRecords (T : TreeRec) : List Record :=
  let obs := T.obligations
  (List.range T.shape.size).map fun j => { kw := T.kw, kb := T.kb, n := T.n, m := 1, extra := obs.getD j [] }

def certRecords : List Record :=
  Data.b0.map (fun wb => { kw := wb.1, kb := wb.2, n := 20, m := 0, extra := [] }) ++
  Data.b1.map (fun wb => { kw := wb.1, kb := wb.2, n := 22, m := 1, extra := [] }) ++
  Data.trees.flatMap treeRecords

def R364 (i : Nat) : Cnf := (certRecords.getD i default).formula.toCnf

def UnsatFacts364 : Prop := UnsatFamily 6921 R364

end Chess.C364
