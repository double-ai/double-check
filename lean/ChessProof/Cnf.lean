namespace Chess

abbrev Clause := Array Int

structure Cnf where
  nv : Nat
  clauses : Array Clause

abbrev Assignment := Nat → Bool

def litVal (a : Assignment) (l : Int) : Bool :=
  if 0 < l then a l.toNat else !a l.natAbs

def Clause.sat (a : Assignment) (c : Clause) : Bool := c.any (litVal a)

namespace Cnf

def Sat (f : Cnf) (a : Assignment) : Prop := ∀ c ∈ f.clauses, c.sat a = true

def Satisfiable (f : Cnf) : Prop := ∃ a, f.Sat a

def Unsat (f : Cnf) : Prop := ∀ a, ¬ f.Sat a

def check (f : Cnf) (a : Assignment) : Bool := f.clauses.all (Clause.sat a)

theorem check_iff (f : Cnf) (a : Assignment) : f.check a = true ↔ f.Sat a := by
  simp only [check, Sat, Array.all_eq_true]
  exact ⟨fun h c hc => let ⟨i, hi, he⟩ := Array.getElem_of_mem hc; he ▸ h i hi,
    fun h i hi => h _ (Array.getElem_mem hi)⟩

theorem Unsat.not_sat {f : Cnf} (h : f.Unsat) (a : Assignment) : ¬ f.Sat a := h a

def WF (f : Cnf) : Prop := ∀ c ∈ f.clauses, ∀ l ∈ c, l ≠ 0 ∧ l.natAbs ≤ f.nv

def wfB (f : Cnf) : Bool := f.clauses.all fun c => c.all fun l => l != 0 && decide (l.natAbs ≤ f.nv)

theorem wfB_iff (f : Cnf) : f.wfB = true ↔ f.WF := by
  simp only [wfB, WF, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]

def clauseLine (c : Clause) : String :=
  " ".intercalate (c.toList.map toString) ++ " 0\n"

def header (f : Cnf) : String :=
  "p cnf " ++ toString f.nv ++ " " ++ toString f.clauses.size ++ "\n"

def dimacs (f : Cnf) : String :=
  f.clauses.foldl (fun s c => s ++ clauseLine c) (header f)

def writeDimacs (f : Cnf) (h : IO.FS.Stream) : IO Unit := do
  h.putStr (header f)
  let mut buf : String := ""
  for c in f.clauses do
    buf := buf ++ clauseLine c
    if buf.utf8ByteSize > 1048576 then
      h.putStr buf
      buf := ""
  h.putStr buf
  h.flush

end Cnf

end Chess
