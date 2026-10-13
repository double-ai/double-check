import ChessProof.C364.Encode

namespace Chess.C364.Tree

open Chess Chess.C364.Fm Chess.C364.Enc

inductive Split where
  | caps
  | chk (k : Nat)
deriving Repr, Inhabited, DecidableEq

inductive Shape where
  | leaf
  | node (sp : Split) (kids : List Shape)
deriving Repr, Inhabited

mutual
def Shape.size : Shape → Nat
  | .leaf => 1
  | .node _ kids => 1 + Shape.sizes kids
def Shape.sizes : List Shape → Nat
  | [] => 0
  | s :: ss => s.size + Shape.sizes ss
end

def combos : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (combos k xs).map (x :: ·) ++ combos (k + 1) xs

def capVars (E : Encoding) : List Int := E.layout.PL.toList.map (·.CAP)

def capsCubes (E : Encoding) : List (List Lit) :=
  let n := E.cfg.n
  (List.range (E.cfg.m + 1)).flatMap fun w =>
    (combos w (List.range n)).map fun S =>
      (List.range n).map fun t => if S.contains t then (capVars E).getD t 0 else -(capVars E).getD t 0

def attAt (E : Encoding) (t x : Nat) : List (Nat × Int) :=
  ((E.layout.AT.getD t #[]).getD x default).A

def chkCubes (E : Encoding) (k : Nat) : List (List Lit) :=
  ((attAt E (k + 1) (1 - E.cfg.col k)).mergeSort fun a b => a.1 ≤ b.1).map fun (_, v) => [v]

def cubes (E : Encoding) (U : List Lit) : Split → List (List Lit)
  | .caps => (capsCubes E).map (U ++ ·)
  | .chk k => (chkCubes E k).map (U ++ ·)

mutual
def obls (E : Encoding) : List Lit → Shape → List (List Clause)
  | U, .leaf => [units U]
  | U, .node sp kids =>
    let ks := cubes E U sp
    (units U ++ ks.map negCube) :: oblsKids E ks kids
def oblsKids (E : Encoding) : List (List Lit) → List Shape → List (List Clause)
  | ks, [] => ks.map units
  | ks, s :: ss => obls E (ks.headD []) s ++ oblsKids E ks.tail ss
end

def CubesOK (E : Encoding) : Prop := ∀ sp, ∀ k ∈ cubes E [] sp, ∀ l ∈ k, l ≠ 0

theorem cubes_nonzero (E : Encoding) (hok : CubesOK E) (U : List Lit) (hU : ∀ l ∈ U, l ≠ 0) (sp : Split) :
    ∀ k ∈ cubes E U sp, ∀ l ∈ k, l ≠ 0 := by
  intro k hk l hl
  cases sp with
  | caps =>
    simp only [cubes, List.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    rcases List.mem_append.mp hl with hl | hl
    · exact hU l hl
    · exact hok .caps c (by simpa [cubes] using hc) l hl
  | chk t =>
    simp only [cubes, List.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    rcases List.mem_append.mp hl with hl | hl
    · exact hU l hl
    · exact hok (.chk t) c (by simpa [cubes] using hc) l hl

mutual
theorem obls_sound (E : Encoding) (hok : CubesOK E) : ∀ (s : Shape) (U : List Lit), (∀ l ∈ U, l ≠ 0) →
    (∀ x ∈ obls E U s, Unsat (E.formula.add x)) → Unsat (E.formula.add (units U))
  | .leaf, U, _, h => h _ (by simp [obls])
  | .node sp kids, U, hU, h => by
    have hz := cubes_nonzero E hok U hU sp
    refine unsat_cover _ U (cubes E U sp) hz (h _ (by simp [obls])) ?_
    exact oblsKids_sound E hok kids (cubes E U sp) hz (fun x hx => h x (by simp [obls, hx]))
theorem oblsKids_sound (E : Encoding) (hok : CubesOK E) : ∀ (ss : List Shape) (ks : List (List Lit)),
    (∀ k ∈ ks, ∀ l ∈ k, l ≠ 0) → (∀ x ∈ oblsKids E ks ss, Unsat (E.formula.add x)) →
    ∀ k ∈ ks, Unsat (E.formula.add (units k))
  | [], ks, _, h => fun k hk => h _ (by simp only [oblsKids, List.mem_map]; exact ⟨k, hk, rfl⟩)
  | s :: ss, ks, hz, h => fun k hk => by
    cases ks with
    | nil => cases hk
    | cons k0 kt =>
      rcases List.mem_cons.mp hk with rfl | hk
      · exact obls_sound E hok s k (hz k (List.mem_cons_self))
          (fun x hx => h x (by simp only [oblsKids, List.headD_cons]; exact List.mem_append_left _ hx))
      · exact oblsKids_sound E hok ss kt (fun k' hk' => hz k' (List.mem_cons_of_mem _ hk'))
          (fun x hx => h x (by simp only [oblsKids, List.tail_cons]; exact List.mem_append_right _ hx)) k hk
end

theorem tree_sound (E : Encoding) (hok : CubesOK E) (s : Shape)
    (h : ∀ x ∈ obls E [] s, Unsat (E.formula.add x)) : Unsat E.formula := by
  have := obls_sound E hok s [] (by simp) h
  simpa [units, Formula.add] using this

structure TreeRec where
  kw : Sq
  kb : Sq
  n : Nat
  shape : Shape
deriving Inhabited

def TreeRec.enc (T : TreeRec) : Encoding := encode T.kw T.kb T.n 1

def TreeRec.obligations (T : TreeRec) : List (List Clause) := obls T.enc [] T.shape

end Chess.C364.Tree
