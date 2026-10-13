import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser
import ChessProof.Cnf

namespace Chess

open Std.Tactic.BVDecide

def Cnf.toStd (f : Cnf) : Std.Sat.CNF Nat :=
  ⟨f.clauses.map fun c => c.toList.map fun l => (l.natAbs - 1, decide (0 < l))⟩

theorem Cnf.lit_toStd (a : Assignment) (l : Int) (h : l ≠ 0) :
    (a (l.natAbs - 1 + 1) == decide (0 < l)) = litVal a l := by
  have e : l.natAbs - 1 + 1 = l.natAbs := by omega
  rw [e]
  unfold litVal
  by_cases hl : 0 < l
  · have : l.toNat = l.natAbs := by omega
    simp [hl, this]
  · simp [hl]

theorem Cnf.toStd_eval (f : Cnf) (a : Assignment) (hz : ∀ c ∈ f.clauses, ∀ l ∈ c, l ≠ 0) :
    f.toStd.eval (fun v => a (v + 1)) = f.check a := by
  rw [Bool.eq_iff_iff]
  simp only [toStd, Std.Sat.CNF.eval, check, Array.all_eq_true_iff_forall_mem, Array.mem_map]
  constructor
  · intro h c hc
    have h1 := h _ ⟨c, hc, rfl⟩
    simp only [Std.Sat.CNF.Clause.eval, List.any_map, List.any_eq_true, Function.comp_apply] at h1
    obtain ⟨l, hl, he⟩ := h1
    have hl' : l ∈ c := Array.mem_toList_iff.mp hl
    simp only [Clause.sat, Array.any_eq_true']
    exact ⟨l, hl', by rw [← Cnf.lit_toStd a l (hz c hc l hl')]; exact he⟩
  · rintro h _ ⟨c, hc, rfl⟩
    have h1 := h c hc
    simp only [Clause.sat, Array.any_eq_true'] at h1
    obtain ⟨l, hl, he⟩ := h1
    simp only [Std.Sat.CNF.Clause.eval, List.any_map, List.any_eq_true, Function.comp_apply]
    exact ⟨l, Array.mem_toList_iff.mpr hl, by rw [Cnf.lit_toStd a l (hz c hc l hl)]; exact he⟩

theorem Cnf.toStd_unsat (f : Cnf) (hw : f.wfB = true) (h : f.toStd.Unsat) : f.Unsat := by
  intro a ha
  have hz : ∀ c ∈ f.clauses, ∀ l ∈ c, l ≠ 0 := fun c hc l hl => ((f.wfB_iff.mp hw) c hc l hl).1
  have h1 := h (fun v => a (v + 1))
  rw [Cnf.toStd_eval f a hz, (Cnf.check_iff f a).mpr ha] at h1
  cases h1

def Cnf.lratOk (f : Cnf) (prf : Array LRAT.IntAction) : Bool := f.wfB && LRAT.check prf f.toStd

def Cnf.lratBytesOk (f : Cnf) (bytes : ByteArray) : Bool :=
  match LRAT.parseLRATProof bytes with
  | .ok prf => f.lratOk prf
  | .error _ => false

theorem Cnf.unsat_of_lratOk (f : Cnf) (prf : Array LRAT.IntAction) (h : f.lratOk prf = true) : f.Unsat := by
  simp only [Cnf.lratOk, Bool.and_eq_true] at h
  exact f.toStd_unsat h.1 (LRAT.check_sound prf f.toStd h.2)

theorem Cnf.unsat_of_lratBytesOk (f : Cnf) (bytes : ByteArray) (h : f.lratBytesOk bytes = true) : f.Unsat := by
  unfold Cnf.lratBytesOk at h
  split at h
  · exact f.unsat_of_lratOk _ h
  · cases h

structure UnsatFamily (n : Nat) (F : Nat → Cnf) : Prop where
  unsat : ∀ i, i < n → (F i).Unsat

structure RouteA (n : Nat) (F : Nat → Cnf) where
  bytes : Nat → ByteArray
  ok : ∀ i, i < n → (F i).lratBytesOk (bytes i) = true

theorem RouteA.family {n : Nat} {F : Nat → Cnf} (r : RouteA n F) : UnsatFamily n F :=
  ⟨fun i h => (F i).unsat_of_lratBytesOk (r.bytes i) (r.ok i h)⟩

theorem UnsatFamily.ofCases {n : Nat} {F : Nat → Cnf} (h : ∀ i, i < n → (F i).Unsat) : UnsatFamily n F := ⟨h⟩

end Chess
