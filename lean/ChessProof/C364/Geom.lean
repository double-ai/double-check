import ChessProof.Spec

namespace Chess.C364

open Chess

def fx (s : Sq) : Int := s.file

def ry (s : Sq) : Int := s.rank

def kdist (a b : Sq) : Nat := max (fx a - fx b).natAbs (ry a - ry b).natAbs

def aligned (a b : Sq) : Bool :=
  a != b && (fx a == fx b || ry a == ry b || (fx a - fx b).natAbs == (ry a - ry b).natAbs)

def collinear (a b z : Sq) : Bool :=
  (fx z - fx a) * (ry b - ry a) == (ry z - ry a) * (fx b - fx a)

def onLine (a b z : Sq) : Bool := aligned a b && collinear a b z

def inSeg (a b z : Sq) : Bool :=
  onLine a b z && z != a && z != b && kdist a z + kdist z b == kdist a b

def seg (a b : Sq) : List Sq := allSq.filter (inSeg a b)

def orthLine (a b : Sq) : Bool := aligned a b && (fx a == fx b || ry a == ry b)

def diagLine (a b : Sq) : Bool := aligned a b && !(fx a == fx b || ry a == ry b)

def knightJump (a b : Sq) : Bool :=
  ((fx a - fx b).natAbs == 1 && (ry a - ry b).natAbs == 2) ||
    ((fx a - fx b).natAbs == 2 && (ry a - ry b).natAbs == 1)

def fileMirror (s : Sq) : Sq := ⟨s.val / 8 * 8 + (7 - s.val % 8), by have := s.isLt; omega⟩

def rankMirror (s : Sq) : Sq := ⟨(7 - s.val / 8) * 8 + s.val % 8, by have := s.isLt; omega⟩

theorem aligned_comm (a b : Sq) : aligned a b = aligned b a := by
  unfold aligned
  have h1 : (fx a - fx b).natAbs = (fx b - fx a).natAbs := by omega
  have h2 : (ry a - ry b).natAbs = (ry b - ry a).natAbs := by omega
  have h3 : (fx a == fx b) = (fx b == fx a) := by
    cases h : fx a == fx b <;> cases h' : fx b == fx a <;> simp_all
  have h4 : (ry a == ry b) = (ry b == ry a) := by
    cases h : ry a == ry b <;> cases h' : ry b == ry a <;> simp_all
  rw [h1, h2, bne_comm, h3, h4]

theorem kdist_comm (a b : Sq) : kdist a b = kdist b a := by
  unfold kdist; omega

theorem mem_allSq (s : Sq) : s ∈ allSq := List.mem_finRange s

def inSegCommCheck : Bool :=
  allSq.all fun a => allSq.all fun b => allSq.all fun z => inSeg a b z == inSeg b a z

set_option maxRecDepth 100000 in
theorem inSegCommCheck_true : inSegCommCheck = true := by decide +kernel

theorem inSeg_comm (a b z : Sq) : inSeg a b z = inSeg b a z := by
  have h := inSegCommCheck_true
  simp only [inSegCommCheck, List.all_eq_true] at h
  exact beq_iff_eq.mp (h a (mem_allSq a) b (mem_allSq b) z (mem_allSq z))

def inSegAlignedCheck : Bool :=
  allSq.all fun a => allSq.all fun b => allSq.all fun z =>
    !(inSeg a b z) || (aligned a z && aligned z b && Nat.ble (kdist a z + 1) (kdist a b))

set_option maxRecDepth 100000 in
theorem inSegAlignedCheck_true : inSegAlignedCheck = true := by decide +kernel

theorem inSeg_aligned (a b z : Sq) (h : inSeg a b z = true) :
    aligned a z = true ∧ aligned z b = true ∧ kdist a z < kdist a b := by
  have hc := inSegAlignedCheck_true
  simp only [inSegAlignedCheck, List.all_eq_true] at hc
  have h2 := hc a (mem_allSq a) b (mem_allSq b) z (mem_allSq z)
  rw [h, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at h2
  exact ⟨h2.1.1, h2.1.2, Nat.le_of_ble_eq_true h2.2⟩

def inSegTransCheck : Bool :=
  allSq.all fun a => allSq.all fun z =>
    (allSq.filter fun w => inSeg a z w).all fun w =>
      (allSq.filter fun b => inSeg a b z).all fun b => inSeg a b w

set_option maxRecDepth 100000 in
theorem inSegTransCheck_true : inSegTransCheck = true := by decide +kernel

theorem inSeg_trans (a b z w : Sq) (hz : inSeg a b z = true) (hw : inSeg a z w = true) :
    inSeg a b w = true := by
  have h := inSegTransCheck_true
  simp only [inSegTransCheck, List.all_eq_true] at h
  have h2 := h a (mem_allSq a) z (mem_allSq z) w (List.mem_filter.mpr ⟨mem_allSq w, hw⟩)
    b (List.mem_filter.mpr ⟨mem_allSq b, hz⟩)
  exact h2

def inSegSplitCheck : Bool :=
  allSq.all fun a => allSq.all fun b =>
    (allSq.filter fun z => inSeg a b z).all fun z =>
      (allSq.filter fun w => inSeg a b w).all fun w =>
        (w == z) || inSeg a z w || inSeg z b w

set_option maxRecDepth 100000 in
theorem inSegSplitCheck_true : inSegSplitCheck = true := by decide +kernel

theorem inSeg_split (a b z w : Sq) (hz : inSeg a b z = true) (hw : inSeg a b w = true) (hne : w ≠ z) :
    inSeg a z w = true ∨ inSeg z b w := by
  have h := inSegSplitCheck_true
  simp only [inSegSplitCheck, List.all_eq_true] at h
  have h2 := h a (mem_allSq a) b (mem_allSq b) z (List.mem_filter.mpr ⟨mem_allSq z, hz⟩)
    w (List.mem_filter.mpr ⟨mem_allSq w, hw⟩)
  rw [beq_eq_false_iff_ne.mpr hne, Bool.false_or, Bool.or_eq_true] at h2
  exact h2

def lemmaGCheck : Bool :=
  allSq.all fun e => allSq.all fun a => allSq.all fun b =>
    !(aligned e a && 2 ≤ kdist a e && kdist a b == 1 && !onLine e a b && 2 ≤ kdist b e) || !aligned b e

set_option maxRecDepth 100000 in
theorem lemmaGCheck_true : lemmaGCheck = true := by decide +kernel

theorem lemmaG (e a b : Sq) (h1 : aligned e a = true) (h2 : 2 ≤ kdist a e) (h3 : kdist a b = 1)
    (h4 : onLine e a b = false) (h5 : 2 ≤ kdist b e) : aligned b e = false := by
  have h := lemmaGCheck_true
  simp only [lemmaGCheck, List.all_eq_true] at h
  have := h e (mem_allSq e) a (mem_allSq a) b (mem_allSq b)
  simp_all

def segDisjCheck : Bool :=
  allSq.all fun k => allSq.all fun z =>
    (allSq.filter fun c => inSeg c k z).all fun c₁ =>
      (allSq.filter fun c => inSeg c k z).all fun c₂ =>
        (c₁ == c₂) || inSeg c₁ k c₂ || inSeg c₂ k c₁

set_option maxRecDepth 100000 in
theorem segDisjCheck_true : segDisjCheck = true := by decide +kernel

theorem seg_disjoint_of_two_lines (k c₁ c₂ z : Sq) (h₁ : inSeg c₁ k z = true) (h₂ : inSeg c₂ k z = true)
    (hc : c₁ ≠ c₂) : inSeg c₁ k c₂ = true ∨ inSeg c₂ k c₁ = true := by
  have h := segDisjCheck_true
  simp only [segDisjCheck, List.all_eq_true] at h
  have h2 := h k (mem_allSq k) z (mem_allSq z) c₁ (List.mem_filter.mpr ⟨mem_allSq c₁, h₁⟩)
    c₂ (List.mem_filter.mpr ⟨mem_allSq c₂, h₂⟩)
  rw [beq_eq_false_iff_ne.mpr hc, Bool.false_or, Bool.or_eq_true] at h2
  exact h2

theorem knightJump_not_aligned (a b : Sq) (h : knightJump a b = true) : aligned a b = false := by
  unfold knightJump at h
  unfold aligned
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  cases h1 : (a != b) <;> simp only [Bool.false_and, Bool.true_and, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  · exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem fileMirror_invol (s : Sq) : fileMirror (fileMirror s) = s := by
  apply Fin.ext; simp only [fileMirror]; omega

theorem rankMirror_invol (s : Sq) : rankMirror (rankMirror s) = s := by
  apply Fin.ext; simp only [rankMirror]; omega

theorem fileMirror_coords (s : Sq) : fx (fileMirror s) = 7 - fx s ∧ ry (fileMirror s) = ry s := by
  simp only [fx, ry, fileMirror, Sq.file, Sq.rank]; omega

theorem rankMirror_coords (s : Sq) : fx (rankMirror s) = fx s ∧ ry (rankMirror s) = 7 - ry s := by
  simp only [fx, ry, rankMirror, Sq.file, Sq.rank]; omega

end Chess.C364
