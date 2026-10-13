namespace Chess.C364.Fm

abbrev Lit := Int

abbrev Clause := List Lit

structure Formula where
  nv : Nat
  clauses : List Clause
deriving Inhabited

abbrev Assign := Nat → Bool

def Lit.eval (σ : Assign) (l : Lit) : Bool :=
  if 0 < l then σ l.toNat else !σ l.natAbs

def Clause.eval (σ : Assign) (c : Clause) : Bool := c.any (Lit.eval σ)

def Formula.eval (σ : Assign) (F : Formula) : Bool := F.clauses.all (Clause.eval σ)

def Sat (F : Formula) : Prop := ∃ σ, F.eval σ = true

def Unsat (F : Formula) : Prop := ¬ Sat F

def Formula.add (F : Formula) (cs : List Clause) : Formula :=
  { F with clauses := F.clauses ++ cs }

def units (us : List Lit) : List Clause := us.map fun u => [u]

def negCube (us : List Lit) : Clause := us.map Neg.neg

theorem eval_add (σ : Assign) (F : Formula) (cs : List Clause) :
    (F.add cs).eval σ = (F.eval σ && cs.all (Clause.eval σ)) := by
  simp [Formula.add, Formula.eval, List.all_append]

theorem unsat_of_add_unsat (F : Formula) (cs : List Clause) (h : Unsat F) : Unsat (F.add cs) := by
  intro ⟨σ, hσ⟩
  rw [eval_add, Bool.and_eq_true] at hσ
  exact h ⟨σ, hσ.1⟩

theorem lit_neg_eval (σ : Assign) (l : Int) (h : l ≠ 0) : Lit.eval σ (-l) = !Lit.eval σ l := by
  unfold Lit.eval
  by_cases hl : 0 < l
  · have h1 : ¬ (0 < -l) := by omega
    have h2 : (-l).natAbs = l.toNat := by omega
    simp only [hl, h1, h2, ↓reduceIte]
  · have h1 : 0 < -l := by omega
    have h2 : (-l).toNat = l.natAbs := by omega
    simp only [hl, h1, h2, ↓reduceIte, Bool.not_not]

theorem eval_units (σ : Assign) (us : List Lit) :
    (units us).all (Clause.eval σ) = us.all (Lit.eval σ) := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [units, Clause.eval] at *; simp [ih]

theorem eval_negCube (σ : Assign) (us : List Lit) (hz : ∀ l ∈ us, l ≠ 0) :
    Clause.eval σ (negCube us) = !us.all (Lit.eval σ) := by
  simp only [Clause.eval, negCube, List.any_map]
  rw [Bool.eq_iff_iff, List.any_eq_true, Bool.not_eq_true', List.all_eq_false]
  constructor
  · rintro ⟨l, hl, he⟩
    refine ⟨l, hl, ?_⟩
    simp only [Function.comp_apply, lit_neg_eval σ l (hz l hl)] at he
    simpa using he
  · rintro ⟨l, hl, he⟩
    refine ⟨l, hl, ?_⟩
    simp only [Function.comp_apply, lit_neg_eval σ l (hz l hl)]
    simpa using he

theorem unsat_cover (F : Formula) (U : List Lit) (kids : List (List Lit))
    (hz : ∀ k ∈ kids, ∀ l ∈ k, l ≠ 0)
    (hcover : Unsat (F.add (units U ++ kids.map negCube)))
    (hkids : ∀ k ∈ kids, Unsat (F.add (units k))) :
    Unsat (F.add (units U)) := by
  intro ⟨σ, hσ⟩
  rw [eval_add, Bool.and_eq_true] at hσ
  apply hcover
  refine ⟨σ, ?_⟩
  rw [eval_add, List.all_append, hσ.1, hσ.2]
  simp only [Bool.true_and, List.all_map, List.all_eq_true, Function.comp_apply]
  intro k hk
  rw [eval_negCube σ k (hz k hk)]
  cases h : k.all (Lit.eval σ)
  · rfl
  · exact absurd ⟨σ, by rw [eval_add, hσ.1, eval_units, h]; rfl⟩ (hkids k hk)

end Chess.C364.Fm
