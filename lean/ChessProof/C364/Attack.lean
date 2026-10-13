import ChessProof.C364.Defs

namespace Chess.C364

open Chess

theorem fx_val (s : Sq) : fx s = ((s.val % 8 : Nat) : Int) := rfl

theorem ry_val (s : Sq) : ry s = ((s.val / 8 : Nat) : Int) := rfl

theorem fx_lt (s : Sq) : fx s < 8 := by
  rw [fx_val]
  exact_mod_cast Nat.mod_lt _ (by decide)

theorem fx_nonneg (s : Sq) : 0 ≤ fx s := by rw [fx_val]; exact Int.natCast_nonneg _

theorem ry_lt (s : Sq) : ry s < 8 := by
  rw [ry_val]
  have h := s.isLt
  have : s.val / 8 < 8 := by omega
  exact_mod_cast this

theorem ry_nonneg (s : Sq) : 0 ≤ ry s := by rw [ry_val]; exact Int.natCast_nonneg _

theorem sq_eq_of_coords (a b : Sq) (hf : fx a = fx b) (hr : ry a = ry b) : a = b := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  have hf' : a.val % 8 = b.val % 8 := by
    rw [fx_val, fx_val] at hf; exact_mod_cast hf
  have hr' : a.val / 8 = b.val / 8 := by
    rw [ry_val, ry_val] at hr; exact_mod_cast hr
  omega

theorem sq_ne_of_coords (a b : Sq) (h : fx a ≠ fx b ∨ ry a ≠ ry b) : a ≠ b := by
  intro e; subst e; rcases h with h | h <;> exact h rfl

theorem sq_ne_coords (a b : Sq) (h : a ≠ b) : ¬(fx a = fx b ∧ ry a = ry b) :=
  fun ⟨h1, h2⟩ => h (sq_eq_of_coords a b h1 h2)

theorem off_eq_some (s t : Sq) (df dr : Int) :
    off s df dr = some t ↔ fx t = fx s + df ∧ ry t = ry s + dr := by
  have es : (s.file : Int) = fx s := rfl
  have esr : (s.rank : Int) = ry s := rfl
  have h1 := fx_nonneg s; have h2 := fx_lt s
  have h3 := ry_nonneg s; have h4 := ry_lt s
  have h5 := fx_nonneg t; have h6 := fx_lt t
  have h7 := ry_nonneg t; have h8 := ry_lt t
  constructor
  · intro h
    by_cases c1 : 0 ≤ (s.file : Int) + df ∧ 0 ≤ (s.rank : Int) + dr
    · by_cases c2 : ((s.file : Int) + df).toNat < 8 ∧ ((s.rank : Int) + dr).toNat < 8
      · simp only [off, mkSq] at h
        rw [if_pos c1, dif_pos c2] at h
        have hval : t.val = Int.toNat ((s.rank : Int) + dr) * 8 + Int.toNat ((s.file : Int) + df) := by
          have h9 := congrArg Fin.val (Option.some.inj h)
          simpa using h9.symm
        have hfN : t.val % 8 = Int.toNat ((s.file : Int) + df) := by omega
        have hrN : t.val / 8 = Int.toNat ((s.rank : Int) + dr) := by omega
        constructor
        · rw [fx_val, hfN, Int.toNat_of_nonneg c1.1, es]
        · rw [ry_val, hrN, Int.toNat_of_nonneg c1.2, esr]
      · have hn : off s df dr = none := by
          simp only [off, mkSq]; rw [if_pos c1, dif_neg c2]
        rw [hn] at h
        exact absurd h (by simp)
    · have hn : off s df dr = none := by
        simp only [off, mkSq]; rw [if_neg c1]
      rw [hn] at h
      exact absurd h (by simp)
  · rintro ⟨hf, hr⟩
    have c1 : 0 ≤ (s.file : Int) + df ∧ 0 ≤ (s.rank : Int) + dr := by
      rw [es, esr]; constructor <;> omega
    have c2 : ((s.file : Int) + df).toNat < 8 ∧ ((s.rank : Int) + dr).toNat < 8 := by
      rw [es, esr]; constructor <;> omega
    have hoff : off s df dr = some ⟨Int.toNat ((s.rank : Int) + dr) * 8 + Int.toNat ((s.file : Int) + df), by omega⟩ := by
      simp only [off, mkSq]; rw [if_pos c1, dif_pos c2]
    rw [hoff]
    apply congrArg some
    apply Fin.ext
    show Int.toNat ((s.rank : Int) + dr) * 8 + Int.toNat ((s.file : Int) + df) = t.val
    have etf : ((t.val % 8 : Nat) : Int) = fx t := (fx_val t).symm
    have etr : ((t.val / 8 : Nat) : Int) = ry t := (ry_val t).symm
    omega

theorem mem_steps (s t : Sq) (ds : List (Int × Int)) :
    t ∈ steps s ds ↔ ∃ d ∈ ds, fx t = fx s + d.1 ∧ ry t = ry s + d.2 := by
  simp only [steps, List.mem_filterMap]
  constructor
  · rintro ⟨⟨df, dr⟩, hd, hoff⟩
    exact ⟨(df, dr), hd, (off_eq_some s t df dr).mp hoff⟩
  · rintro ⟨⟨df, dr⟩, hd, hf, hr⟩
    exact ⟨(df, dr), hd, (off_eq_some s t df dr).mpr ⟨hf, hr⟩⟩

theorem int_succ_mul (k : Nat) (x : Int) : ((k + 1 : Nat) : Int) * x = (k : Int) * x + x := by
  induction k with
  | zero =>
    show (1 : Int) * x = 0 * x + x
    rw [Int.one_mul, Int.zero_mul, Int.zero_add]
  | succ k ih =>
    have e : ((k + 1 + 1 : Nat) : Int) = ((k + 1 : Nat) : Int) + 1 := by omega
    rw [e, Int.add_mul, Int.one_mul, ih]

theorem off_none_range {s : Sq} {df dr : Int} (h : off s df dr = none) :
    fx s + df < 0 ∨ 7 < fx s + df ∨ ry s + dr < 0 ∨ 7 < ry s + dr := by
  by_cases h1 : fx s + df < 0
  · exact Or.inl h1
  · by_cases h2 : 7 < fx s + df
    · exact Or.inr (Or.inl h2)
    · by_cases h3 : ry s + dr < 0
      · exact Or.inr (Or.inr (Or.inl h3))
      · by_cases h4 : 7 < ry s + dr
        · exact Or.inr (Or.inr (Or.inr h4))
        · exfalso
          have es : (s.file : Int) = fx s := rfl
          have esr : (s.rank : Int) = ry s := rfl
          have c1 : 0 ≤ (s.file : Int) + df ∧ 0 ≤ (s.rank : Int) + dr := by
            constructor <;> omega
          have c2 : ((s.file : Int) + df).toNat < 8 ∧ ((s.rank : Int) + dr).toNat < 8 := by
            constructor <;> omega
          have hoff : off s df dr =
              some ⟨(Int.toNat ((s.rank : Int) + dr)) * 8 + Int.toNat ((s.file : Int) + df), by omega⟩ := by
            simp only [off, mkSq]
            rw [if_pos c1, dif_pos c2]
          rw [hoff] at h
          exact absurd h (by simp)

theorem off_none_step {s t : Sq} {df dr : Int} (h : off s df dr = none)
    {k : Nat} (hk : 1 ≤ k) (hfx : fx t = fx s + k * df) (hry : ry t = ry s + k * dr) : False := by
  have hr := off_none_range h
  have b1 := fx_nonneg s; have b2 := fx_lt s
  have b3 := ry_nonneg s; have b4 := ry_lt s
  have b5 := fx_nonneg t; have b6 := fx_lt t
  have b7 := ry_nonneg t; have b8 := ry_lt t
  rcases hr with hc | hc | hc | hc
  · have hh1 : (0 : Int) ≤ ((k : Int) - 1) * (-df) := Int.mul_nonneg (by omega) (by omega)
    rw [Int.mul_neg, Int.sub_mul, Int.one_mul] at hh1
    omega
  · have hh1 : (0 : Int) ≤ ((k : Int) - 1) * df := Int.mul_nonneg (by omega) (by omega)
    rw [Int.sub_mul, Int.one_mul] at hh1
    omega
  · have hh1 : (0 : Int) ≤ ((k : Int) - 1) * (-dr) := Int.mul_nonneg (by omega) (by omega)
    rw [Int.mul_neg, Int.sub_mul, Int.one_mul] at hh1
    omega
  · have hh1 : (0 : Int) ≤ ((k : Int) - 1) * dr := Int.mul_nonneg (by omega) (by omega)
    rw [Int.sub_mul, Int.one_mul] at hh1
    omega

theorem ray_none (b : Board) (s : Sq) (df dr : Int) (n : Nat) (h : off s df dr = none) :
    ray b s df dr (n + 1) = [] := by
  show (match off s df dr with | none => [] | some u => if empty b u then u :: ray b u df dr n else [u]) = []
  rw [h]

theorem ray_some (b : Board) (s u : Sq) (df dr : Int) (n : Nat) (h : off s df dr = some u) :
    ray b s df dr (n + 1) = if empty b u then u :: ray b u df dr n else [u] := by
  show (match off s df dr with | none => [] | some u => if empty b u then u :: ray b u df dr n else [u]) =
    if empty b u then u :: ray b u df dr n else [u]
  rw [h]

theorem mem_ray (b : Board) (s t : Sq) (df dr : Int) (n : Nat) :
    t ∈ ray b s df dr n ↔
      ∃ k : Nat, 1 ≤ k ∧ k ≤ n ∧ fx t = fx s + k * df ∧ ry t = ry s + k * dr ∧
        ∀ j : Nat, 1 ≤ j → j < k → ∀ z : Sq, fx z = fx s + j * df → ry z = ry s + j * dr → b z = none := by
  induction n generalizing s with
  | zero =>
    constructor
    · intro h
      simp only [ray, List.not_mem_nil] at h
    · rintro ⟨k, hk1, hkn, -, -, -⟩
      omega
  | succ n ih =>
    cases hoff : off s df dr with
    | none =>
      rw [ray_none b s df dr n hoff]
      constructor
      · intro h
        simp only [List.not_mem_nil] at h
      · rintro ⟨k, hk1, hkn, hfx, hry, hmid⟩
        exact (off_none_step hoff hk1 hfx hry).elim
    | some u =>
      rw [ray_some b s u df dr n hoff]
      obtain ⟨hux, huy⟩ := (off_eq_some s u df dr).mp hoff
      by_cases he : empty b u = true
      · rw [if_pos he]
        have hu_none : b u = none := Option.isNone_iff_eq_none.mp he
        constructor
        · intro h
          rw [List.mem_cons] at h
          rcases h with htu | htail
          · rw [htu]
            refine ⟨1, by omega, by omega, by simpa using hux, by simpa using huy, ?_⟩
            intro j hj1 hjk
            exfalso
            omega
          · obtain ⟨k', hk'1, hk'n, hfx', hry', hmid'⟩ := (ih u).mp htail
            refine ⟨k' + 1, by omega, by omega, ?_, ?_, ?_⟩
            · rw [int_succ_mul]
              omega
            · rw [int_succ_mul]
              omega
            · intro j hj1 hjk z hzx hzy
              by_cases hjj : j = 1
              · subst hjj
                have e1 : fx z = fx s + df := by simpa using hzx
                have e2 : ry z = ry s + dr := by simpa using hzy
                rw [sq_eq_of_coords z u (by omega) (by omega)]
                exact hu_none
              · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
                rw [int_succ_mul] at hzx
                rw [int_succ_mul] at hzy
                exact hmid' j' (by omega) (by omega) z (by omega) (by omega)
        · rintro ⟨k, hk1, hkn, hfx, hry, hmid⟩
          rw [List.mem_cons]
          by_cases hk : k = 1
          · subst hk
            have e1 : fx t = fx s + df := by simpa using hfx
            have e2 : ry t = ry s + dr := by simpa using hry
            exact Or.inl (sq_eq_of_coords t u (by omega) (by omega))
          · right
            obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            rw [int_succ_mul] at hfx
            rw [int_succ_mul] at hry
            apply (ih u).mpr
            refine ⟨k', by omega, by omega, by omega, by omega, ?_⟩
            intro j hj1 hjk z hzx hzy
            have e1 : fx z = fx s + ((j + 1 : Nat) : Int) * df := by
              rw [int_succ_mul]
              omega
            have e2 : ry z = ry s + ((j + 1 : Nat) : Int) * dr := by
              rw [int_succ_mul]
              omega
            exact hmid (j + 1) (by omega) (by omega) z e1 e2
      · rw [if_neg he]
        have hu_some : b u ≠ none := by
          intro hn
          exact he (Option.isNone_iff_eq_none.mpr hn)
        constructor
        · intro h
          rw [List.mem_singleton] at h
          rw [h]
          refine ⟨1, by omega, by omega, by simpa using hux, by simpa using huy, ?_⟩
          intro j hj1 hjk
          exfalso
          omega
        · rintro ⟨k, hk1, hkn, hfx, hry, hmid⟩
          by_cases hk : k = 1
          · subst hk
            have e1 : fx t = fx s + df := by simpa using hfx
            have e2 : ry t = ry s + dr := by simpa using hry
            rw [sq_eq_of_coords t u (by omega) (by omega)]
            exact List.mem_singleton_self _
          · exfalso
            apply hu_some
            exact hmid 1 (by omega) (by omega) u (by simpa using hux) (by simpa using huy)

theorem int_mul_cancel (A B : Int) (k : Nat) (hk : 1 ≤ k) (h : A * k = B * k) : A = B := by
  have hk0 : (k : Int) ≠ 0 := by omega
  have h0 : (A - B) * (k : Int) = 0 := by rw [Int.sub_mul, h, Int.sub_self]
  rcases Int.mul_eq_zero.mp h0 with h1 | h2
  · exact Int.sub_eq_zero.mp h1
  · exact absurd h2 hk0

theorem int_mul_cancel_zero (A : Int) (k : Nat) (hk : 1 ≤ k) (h : A * k = 0) : A = 0 := by
  have hk0 : (k : Int) ≠ 0 := by omega
  rcases Int.mul_eq_zero.mp h with h1 | h2
  · exact h1
  · exact absurd h2 hk0

theorem int_mul_swap_lits (A B a b : Int) : (A * a) * (B * b) = (A * b) * (B * a) := by
  have i1 : (A * a) * (B * b) = (A * B) * (b * a) := by
    rw [Int.mul_assoc, ← Int.mul_assoc a B b, Int.mul_comm a B, Int.mul_assoc B a b,
      ← Int.mul_assoc A B (a * b), Int.mul_comm a b]
  have i2 : (A * b) * (B * a) = (A * B) * (b * a) := by
    rw [Int.mul_assoc, ← Int.mul_assoc b B a, Int.mul_comm b B, Int.mul_assoc B b a,
      ← Int.mul_assoc A B (b * a)]
  rw [i1, i2]

theorem queenD_decomp (d : Int × Int) (hd : d ∈ queenD) :
    d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1) ∨
      d = (1, 1) ∨ d = (1, -1) ∨ d = (-1, 1) ∨ d = (-1, -1) := by
  simp only [queenD, rookD, bishopD, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with (h | h | h | h) | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

set_option maxHeartbeats 800000 in
theorem seg_step (s t z : Sq) (d : Int × Int) (hd : d ∈ queenD) (k : Nat) (hk : 1 ≤ k)
    (htx : fx t = fx s + (k : Int) * d.1) (hty : ry t = ry s + (k : Int) * d.2)
    (hz : inSeg s t z = true) :
    ∃ j : Nat, 1 ≤ j ∧ j < k ∧ fx z = fx s + (j : Int) * d.1 ∧ ry z = ry s + (j : Int) * d.2 := by
  have a1 := fx_nonneg s; have a2 := fx_lt s
  have a3 := ry_nonneg s; have a4 := ry_lt s
  have a5 := fx_nonneg t; have a6 := fx_lt t
  have a7 := ry_nonneg t; have a8 := ry_lt t
  have a9 := fx_nonneg z; have a10 := fx_lt z
  have a11 := ry_nonneg z; have a12 := ry_lt z
  simp only [inSeg, onLine, aligned, collinear, kdist, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
    Bool.or_eq_true] at hz
  obtain ⟨h4z, hkd⟩ := hz
  obtain ⟨h3z, hz_t⟩ := h4z
  obtain ⟨h2z, hz_s⟩ := h3z
  obtain ⟨h1z, hcol⟩ := h2z
  obtain ⟨hne_st, _hor⟩ := h1z
  have hzne_s : fx z ≠ fx s ∨ ry z ≠ ry s := by
    by_cases hc : fx z = fx s
    · right; intro hry'; exact hz_s (sq_eq_of_coords z s hc hry')
    · left; exact hc
  have hzne_t : fx z ≠ fx t ∨ ry z ≠ ry t := by
    by_cases hc : fx z = fx t
    · right; intro hry'; exact hz_t (sq_eq_of_coords z t hc hry')
    · left; exact hc
  rcases queenD_decomp d hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only at htx hty ⊢
    have e3 : fx t - fx s = (k : Int) := by omega
    have e4 : ry t - ry s = 0 := by omega
    rw [e4, Int.mul_zero, e3] at hcol
    have hrel : ry z - ry s = 0 := int_mul_cancel_zero _ k hk hcol.symm
    refine ⟨(fx z - fx s).toNat, by omega, by omega, by omega, by omega⟩
  · dsimp only at htx hty ⊢
    have m2 : (ry z - ry s) * (-(k : Int)) = (-(ry z - ry s)) * (k : Int) := by
      rw [Int.mul_neg, Int.neg_mul]
    have e3 : fx t - fx s = -(k : Int) := by omega
    have e4 : ry t - ry s = 0 := by omega
    rw [e4, Int.mul_zero, e3, m2] at hcol
    have hm : -(ry z - ry s) = 0 := int_mul_cancel_zero _ k hk hcol.symm
    have hrel : ry z - ry s = 0 := by omega
    refine ⟨(-(fx z - fx s)).toNat, by omega, by omega, by omega, by omega⟩
  · dsimp only at htx hty ⊢
    have e3 : fx t - fx s = 0 := by omega
    have e4 : ry t - ry s = (k : Int) := by omega
    rw [e4, e3, Int.mul_zero] at hcol
    have hrel : fx z - fx s = 0 := int_mul_cancel_zero _ k hk hcol
    refine ⟨(ry z - ry s).toNat, by omega, by omega, by omega, by omega⟩
  · dsimp only at htx hty ⊢
    have m1 : (fx z - fx s) * (-(k : Int)) = (-(fx z - fx s)) * (k : Int) := by
      rw [Int.mul_neg, Int.neg_mul]
    have e3 : fx t - fx s = 0 := by omega
    have e4 : ry t - ry s = -(k : Int) := by omega
    rw [e4, m1, e3, Int.mul_zero] at hcol
    have hm : -(fx z - fx s) = 0 := int_mul_cancel_zero _ k hk hcol
    have hrel : fx z - fx s = 0 := by omega
    refine ⟨(-(ry z - ry s)).toNat, by omega, by omega, by omega, by omega⟩
  · dsimp only at htx hty ⊢
    have e3 : fx t - fx s = (k : Int) := by omega
    have e4 : ry t - ry s = (k : Int) := by omega
    rw [e4, e3] at hcol
    have hrel : fx z - fx s = ry z - ry s := int_mul_cancel _ _ k hk hcol
    refine ⟨(fx z - fx s).toNat, by omega, by omega, by omega, by omega⟩
  · dsimp only at htx hty ⊢
    have m1 : (fx z - fx s) * (-(k : Int)) = (-(fx z - fx s)) * (k : Int) := by
      rw [Int.mul_neg, Int.neg_mul]
    have e3 : fx t - fx s = (k : Int) := by omega
    have e4 : ry t - ry s = -(k : Int) := by omega
    rw [e4, e3, m1] at hcol
    have hrel : -(fx z - fx s) = ry z - ry s := int_mul_cancel _ _ k hk hcol
    refine ⟨(fx z - fx s).toNat, by omega, by omega, by omega, by omega⟩
  · dsimp only at htx hty ⊢
    have m2 : (ry z - ry s) * (-(k : Int)) = (-(ry z - ry s)) * (k : Int) := by
      rw [Int.mul_neg, Int.neg_mul]
    have e3 : fx t - fx s = -(k : Int) := by omega
    have e4 : ry t - ry s = (k : Int) := by omega
    rw [e4, e3, m2] at hcol
    have hrel : fx z - fx s = -(ry z - ry s) := int_mul_cancel _ _ k hk hcol
    refine ⟨(ry z - ry s).toNat, by omega, by omega, by omega, by omega⟩
  · dsimp only at htx hty ⊢
    have m1 : (fx z - fx s) * (-(k : Int)) = (-(fx z - fx s)) * (k : Int) := by
      rw [Int.mul_neg, Int.neg_mul]
    have m2 : (ry z - ry s) * (-(k : Int)) = (-(ry z - ry s)) * (k : Int) := by
      rw [Int.mul_neg, Int.neg_mul]
    have e3 : fx t - fx s = -(k : Int) := by omega
    have e4 : ry t - ry s = -(k : Int) := by omega
    rw [e4, e3, m1, m2] at hcol
    have hrel : -(fx z - fx s) = -(ry z - ry s) := int_mul_cancel _ _ k hk hcol
    refine ⟨(-(ry z - ry s)).toNat, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 800000 in
theorem step_seg (s t z : Sq) (d : Int × Int) (hd : d ∈ queenD) (k j : Nat)
    (hk : 1 ≤ k) (hj : 1 ≤ j) (hjk : j < k)
    (htx : fx t = fx s + (k : Int) * d.1) (hty : ry t = ry s + (k : Int) * d.2)
    (hzx : fx z = fx s + (j : Int) * d.1) (hzy : ry z = ry s + (j : Int) * d.2) :
    inSeg s t z = true := by
  have a1 := fx_nonneg s; have a2 := fx_lt s
  have a3 := ry_nonneg s; have a4 := ry_lt s
  have a5 := fx_nonneg t; have a6 := fx_lt t
  have a7 := ry_nonneg t; have a8 := ry_lt t
  have a9 := fx_nonneg z; have a10 := fx_lt z
  have a11 := ry_nonneg z; have a12 := ry_lt z
  simp only [inSeg, onLine, aligned, collinear, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
    Bool.or_eq_true]
  rcases queenD_decomp d hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only at htx hty hzx hzy
    have e1 : fx z - fx s = (j : Int) * 1 := by omega
    have e2 : ry z - ry s = (j : Int) * 0 := by omega
    have e3 : fx t - fx s = (k : Int) * 1 := by omega
    have e4 : ry t - ry s = (k : Int) * 0 := by omega
    have hcoll : (fx z - fx s) * (ry t - ry s) = (ry z - ry s) * (fx t - fx s) := by
      rw [e1, e2, e3, e4]; exact int_mul_swap_lits _ _ _ _
    have hkd : kdist s z + kdist z t = kdist s t := by
      simp only [kdist]; omega
    have hne : s ≠ t := sq_ne_of_coords s t (Or.inl (by omega))
    have hdj : (fx s = fx t ∨ ry s = ry t) ∨ (fx s - fx t).natAbs = (ry s - ry t).natAbs := Or.inl (Or.inr (by omega))
    have hzs : z ≠ s := sq_ne_of_coords z s (Or.inl (by omega))
    have hzt : z ≠ t := sq_ne_of_coords z t (Or.inl (by omega))
    exact ⟨⟨⟨⟨⟨hne, hdj⟩, hcoll⟩, hzs⟩, hzt⟩, hkd⟩
  · dsimp only at htx hty hzx hzy
    have e1 : fx z - fx s = (j : Int) * (-1) := by omega
    have e2 : ry z - ry s = (j : Int) * 0 := by omega
    have e3 : fx t - fx s = (k : Int) * (-1) := by omega
    have e4 : ry t - ry s = (k : Int) * 0 := by omega
    have hcoll : (fx z - fx s) * (ry t - ry s) = (ry z - ry s) * (fx t - fx s) := by
      rw [e1, e2, e3, e4]; exact int_mul_swap_lits _ _ _ _
    have hkd : kdist s z + kdist z t = kdist s t := by
      simp only [kdist]; omega
    have hne : s ≠ t := sq_ne_of_coords s t (Or.inl (by omega))
    have hdj : (fx s = fx t ∨ ry s = ry t) ∨ (fx s - fx t).natAbs = (ry s - ry t).natAbs := Or.inl (Or.inr (by omega))
    have hzs : z ≠ s := sq_ne_of_coords z s (Or.inl (by omega))
    have hzt : z ≠ t := sq_ne_of_coords z t (Or.inl (by omega))
    exact ⟨⟨⟨⟨⟨hne, hdj⟩, hcoll⟩, hzs⟩, hzt⟩, hkd⟩
  · dsimp only at htx hty hzx hzy
    have e1 : fx z - fx s = (j : Int) * 0 := by omega
    have e2 : ry z - ry s = (j : Int) * 1 := by omega
    have e3 : fx t - fx s = (k : Int) * 0 := by omega
    have e4 : ry t - ry s = (k : Int) * 1 := by omega
    have hcoll : (fx z - fx s) * (ry t - ry s) = (ry z - ry s) * (fx t - fx s) := by
      rw [e1, e2, e3, e4]; exact int_mul_swap_lits _ _ _ _
    have hkd : kdist s z + kdist z t = kdist s t := by
      simp only [kdist]; omega
    have hne : s ≠ t := sq_ne_of_coords s t (Or.inr (by omega))
    have hdj : (fx s = fx t ∨ ry s = ry t) ∨ (fx s - fx t).natAbs = (ry s - ry t).natAbs := Or.inl (Or.inl (by omega))
    have hzs : z ≠ s := sq_ne_of_coords z s (Or.inr (by omega))
    have hzt : z ≠ t := sq_ne_of_coords z t (Or.inr (by omega))
    exact ⟨⟨⟨⟨⟨hne, hdj⟩, hcoll⟩, hzs⟩, hzt⟩, hkd⟩
  · dsimp only at htx hty hzx hzy
    have e1 : fx z - fx s = (j : Int) * 0 := by omega
    have e2 : ry z - ry s = (j : Int) * (-1) := by omega
    have e3 : fx t - fx s = (k : Int) * 0 := by omega
    have e4 : ry t - ry s = (k : Int) * (-1) := by omega
    have hcoll : (fx z - fx s) * (ry t - ry s) = (ry z - ry s) * (fx t - fx s) := by
      rw [e1, e2, e3, e4]; exact int_mul_swap_lits _ _ _ _
    have hkd : kdist s z + kdist z t = kdist s t := by
      simp only [kdist]; omega
    have hne : s ≠ t := sq_ne_of_coords s t (Or.inr (by omega))
    have hdj : (fx s = fx t ∨ ry s = ry t) ∨ (fx s - fx t).natAbs = (ry s - ry t).natAbs := Or.inl (Or.inl (by omega))
    have hzs : z ≠ s := sq_ne_of_coords z s (Or.inr (by omega))
    have hzt : z ≠ t := sq_ne_of_coords z t (Or.inr (by omega))
    exact ⟨⟨⟨⟨⟨hne, hdj⟩, hcoll⟩, hzs⟩, hzt⟩, hkd⟩
  · dsimp only at htx hty hzx hzy
    have e1 : fx z - fx s = (j : Int) * 1 := by omega
    have e2 : ry z - ry s = (j : Int) * 1 := by omega
    have e3 : fx t - fx s = (k : Int) * 1 := by omega
    have e4 : ry t - ry s = (k : Int) * 1 := by omega
    have hcoll : (fx z - fx s) * (ry t - ry s) = (ry z - ry s) * (fx t - fx s) := by
      rw [e1, e2, e3, e4]
    have hkd : kdist s z + kdist z t = kdist s t := by
      simp only [kdist]; omega
    have hne : s ≠ t := sq_ne_of_coords s t (Or.inl (by omega))
    have hdj : (fx s = fx t ∨ ry s = ry t) ∨ (fx s - fx t).natAbs = (ry s - ry t).natAbs := Or.inr (by omega)
    have hzs : z ≠ s := sq_ne_of_coords z s (Or.inl (by omega))
    have hzt : z ≠ t := sq_ne_of_coords z t (Or.inl (by omega))
    exact ⟨⟨⟨⟨⟨hne, hdj⟩, hcoll⟩, hzs⟩, hzt⟩, hkd⟩
  · dsimp only at htx hty hzx hzy
    have e1 : fx z - fx s = (j : Int) * 1 := by omega
    have e2 : ry z - ry s = (j : Int) * (-1) := by omega
    have e3 : fx t - fx s = (k : Int) * 1 := by omega
    have e4 : ry t - ry s = (k : Int) * (-1) := by omega
    have hcoll : (fx z - fx s) * (ry t - ry s) = (ry z - ry s) * (fx t - fx s) := by
      rw [e1, e2, e3, e4]; exact int_mul_swap_lits _ _ _ _
    have hkd : kdist s z + kdist z t = kdist s t := by
      simp only [kdist]; omega
    have hne : s ≠ t := sq_ne_of_coords s t (Or.inl (by omega))
    have hdj : (fx s = fx t ∨ ry s = ry t) ∨ (fx s - fx t).natAbs = (ry s - ry t).natAbs := Or.inr (by omega)
    have hzs : z ≠ s := sq_ne_of_coords z s (Or.inl (by omega))
    have hzt : z ≠ t := sq_ne_of_coords z t (Or.inl (by omega))
    exact ⟨⟨⟨⟨⟨hne, hdj⟩, hcoll⟩, hzs⟩, hzt⟩, hkd⟩
  · dsimp only at htx hty hzx hzy
    have e1 : fx z - fx s = (j : Int) * (-1) := by omega
    have e2 : ry z - ry s = (j : Int) * 1 := by omega
    have e3 : fx t - fx s = (k : Int) * (-1) := by omega
    have e4 : ry t - ry s = (k : Int) * 1 := by omega
    have hcoll : (fx z - fx s) * (ry t - ry s) = (ry z - ry s) * (fx t - fx s) := by
      rw [e1, e2, e3, e4]; exact int_mul_swap_lits _ _ _ _
    have hkd : kdist s z + kdist z t = kdist s t := by
      simp only [kdist]; omega
    have hne : s ≠ t := sq_ne_of_coords s t (Or.inl (by omega))
    have hdj : (fx s = fx t ∨ ry s = ry t) ∨ (fx s - fx t).natAbs = (ry s - ry t).natAbs := Or.inr (by omega)
    have hzs : z ≠ s := sq_ne_of_coords z s (Or.inl (by omega))
    have hzt : z ≠ t := sq_ne_of_coords z t (Or.inl (by omega))
    exact ⟨⟨⟨⟨⟨hne, hdj⟩, hcoll⟩, hzs⟩, hzt⟩, hkd⟩
  · dsimp only at htx hty hzx hzy
    have e1 : fx z - fx s = (j : Int) * (-1) := by omega
    have e2 : ry z - ry s = (j : Int) * (-1) := by omega
    have e3 : fx t - fx s = (k : Int) * (-1) := by omega
    have e4 : ry t - ry s = (k : Int) * (-1) := by omega
    have hcoll : (fx z - fx s) * (ry t - ry s) = (ry z - ry s) * (fx t - fx s) := by
      rw [e1, e2, e3, e4]
    have hkd : kdist s z + kdist z t = kdist s t := by
      simp only [kdist]; omega
    have hne : s ≠ t := sq_ne_of_coords s t (Or.inl (by omega))
    have hdj : (fx s = fx t ∨ ry s = ry t) ∨ (fx s - fx t).natAbs = (ry s - ry t).natAbs := Or.inr (by omega)
    have hzs : z ≠ s := sq_ne_of_coords z s (Or.inl (by omega))
    have hzt : z ≠ t := sq_ne_of_coords z t (Or.inl (by omega))
    exact ⟨⟨⟨⟨⟨hne, hdj⟩, hcoll⟩, hzs⟩, hzt⟩, hkd⟩

theorem mem_rays_iff (b : Board) (s t : Sq) (ds : List (Int × Int)) (hds : ∀ d ∈ ds, d ∈ queenD) :
    t ∈ rays b s ds ↔
      ∃ d ∈ ds, ∃ k : Nat, 1 ≤ k ∧ fx t = fx s + k * d.1 ∧ ry t = ry s + k * d.2 ∧ clearPath b s t := by
  simp only [rays, List.mem_flatMap]
  constructor
  · rintro ⟨⟨df, dr⟩, hd, hray⟩
    obtain ⟨k, hk1, hk7, hfx, hry, hmid⟩ := (mem_ray b s t df dr 7).mp hray
    refine ⟨(df, dr), hd, k, hk1, hfx, hry, ?_⟩
    intro z hseg
    obtain ⟨j, hj1, hjk, hzx, hzy⟩ := seg_step s t z (df, dr) (hds _ hd) k hk1 hfx hry hseg
    exact hmid j hj1 hjk z hzx hzy
  · rintro ⟨⟨df, dr⟩, hd, k, hk1, hfx, hry, hclear⟩
    refine ⟨(df, dr), hd, ?_⟩
    have a1 := fx_nonneg s; have a2 := fx_lt s
    have a3 := ry_nonneg s; have a4 := ry_lt s
    have a5 := fx_nonneg t; have a6 := fx_lt t
    have a7 := ry_nonneg t; have a8 := ry_lt t
    have hk7 : k ≤ 7 := by
      rcases queenD_decomp (df, dr) (hds _ hd) with h | h | h | h | h | h | h | h <;>
        (rw [Prod.mk.injEq] at h; obtain ⟨hd1, hd2⟩ := h; dsimp only at hfx hry; subst hd1; subst hd2; omega)
    refine ((mem_ray b s t df dr 7).mpr ⟨k, hk1, hk7, hfx, hry, ?_⟩)
    intro j hj1 hjk z hzx hzy
    exact hclear z (step_seg s t z (df, dr) (hds _ hd) k j hk1 hj1 hjk hfx hry hzx hzy)

def isig (x : Int) : Int := if 0 ≤ x then 1 else -1

theorem rookD_isig_r (y : Int) : ((0 : Int), isig y) ∈ rookD := by
  show ((0, if 0 ≤ y then 1 else -1) : Int × Int) ∈ rookD
  by_cases h : 0 ≤ y
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

theorem rookD_isig_l (x : Int) : (isig x, (0 : Int)) ∈ rookD := by
  show ((if 0 ≤ x then 1 else -1, 0) : Int × Int) ∈ rookD
  by_cases h : 0 ≤ x
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

theorem bishopD_isig (x y : Int) : (isig x, isig y) ∈ bishopD := by
  show ((if 0 ≤ x then 1 else -1, if 0 ≤ y then 1 else -1) : Int × Int) ∈ bishopD
  by_cases h1 : 0 ≤ x <;> by_cases h2 : 0 ≤ y
  · rw [if_pos h1, if_pos h2]; decide
  · rw [if_pos h1, if_neg h2]; decide
  · rw [if_neg h1, if_pos h2]; decide
  · rw [if_neg h1, if_neg h2]; decide

theorem int_mul_isig (x : Int) : (x.natAbs : Int) * isig x = x := by
  show (x.natAbs : Int) * (if 0 ≤ x then 1 else -1) = x
  by_cases h : 0 ≤ x
  · rw [if_pos h, Int.mul_one]; omega
  · rw [if_neg h, Int.mul_neg_one]; omega

theorem mem_queenD_of (x y : Int)
    (hx : x = 0 ∨ x = 1 ∨ x = -1) (hy : y = 0 ∨ y = 1 ∨ y = -1)
    (hne : ¬(x = 0 ∧ y = 0)) :
    (x, y) ∈ queenD := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | decide | exact absurd ⟨rfl, rfl⟩ hne

theorem rookD_sub_queenD (d : Int × Int) (hd : d ∈ rookD) : d ∈ queenD := by
  rw [queenD, List.mem_append]; exact Or.inl hd

theorem bishopD_sub_queenD (d : Int × Int) (hd : d ∈ bishopD) : d ∈ queenD := by
  rw [queenD, List.mem_append]; exact Or.inr hd

theorem mem_attacks_iff (b : Board) (s t : Sq) (q : Piece) :
    t ∈ attacks b s q ↔ geomAttack q.color q.kind s t = true ∧ (isSlider q.kind = true → clearPath b s t) := by
  cases q with
  | mk c k =>
  cases k
  · cases c
    · constructor
      · intro h
        have h2 : t ∈ steps s [(1, (1:Int)), (-1, 1)] := h
        obtain ⟨d, hd, hfx, hry⟩ := (mem_steps s t _).mp h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> dsimp only at hfx hry
        · refine ⟨?_, fun hi => absurd hi (by decide)⟩
          simp only [geomAttack, Color.fwd, Bool.and_eq_true, beq_iff_eq]
          exact ⟨by omega, by omega⟩
        · refine ⟨?_, fun hi => absurd hi (by decide)⟩
          simp only [geomAttack, Color.fwd, Bool.and_eq_true, beq_iff_eq]
          exact ⟨by omega, by omega⟩
      · rintro ⟨hg, -⟩
        show t ∈ steps s [(1, (1:Int)), (-1, 1)]
        simp only [geomAttack, Color.fwd, Bool.and_eq_true, beq_iff_eq] at hg
        obtain ⟨hry, hfx⟩ := hg
        by_cases hs : 0 ≤ fx t - fx s
        · exact (mem_steps s t _).mpr ⟨(1, 1), by decide, by omega, by omega⟩
        · exact (mem_steps s t _).mpr ⟨(-1, 1), by decide, by omega, by omega⟩
    · constructor
      · intro h
        have h2 : t ∈ steps s [(1, (-1:Int)), (-1, -1)] := h
        obtain ⟨d, hd, hfx, hry⟩ := (mem_steps s t _).mp h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> dsimp only at hfx hry
        · refine ⟨?_, fun hi => absurd hi (by decide)⟩
          simp only [geomAttack, Color.fwd, Bool.and_eq_true, beq_iff_eq]
          exact ⟨by omega, by omega⟩
        · refine ⟨?_, fun hi => absurd hi (by decide)⟩
          simp only [geomAttack, Color.fwd, Bool.and_eq_true, beq_iff_eq]
          exact ⟨by omega, by omega⟩
      · rintro ⟨hg, -⟩
        show t ∈ steps s [(1, (-1:Int)), (-1, -1)]
        simp only [geomAttack, Color.fwd, Bool.and_eq_true, beq_iff_eq] at hg
        obtain ⟨hry, hfx⟩ := hg
        by_cases hs : 0 ≤ fx t - fx s
        · exact (mem_steps s t _).mpr ⟨(1, -1), by decide, by omega, by omega⟩
        · exact (mem_steps s t _).mpr ⟨(-1, -1), by decide, by omega, by omega⟩
  · constructor
    · intro h
      have h2 : t ∈ steps s knightD := h
      obtain ⟨d, hd, hfx, hry⟩ := (mem_steps s t _).mp h2
      simp only [knightD, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hfx hry
      all_goals refine ⟨?_, fun hi => absurd hi (show isSlider Kind.knight ≠ true from by decide)⟩
      all_goals simp only [geomAttack, knightJump, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      all_goals omega
    · rintro ⟨hg, -⟩
      show t ∈ steps s knightD
      simp only [geomAttack, knightJump, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hg
      have hx : fx t - fx s = 1 ∨ fx t - fx s = -1 ∨ fx t - fx s = 2 ∨ fx t - fx s = -2 := by omega
      have hy : ry t - ry s = 1 ∨ ry t - ry s = -1 ∨ ry t - ry s = 2 ∨ ry t - ry s = -2 := by omega
      refine (mem_steps s t knightD).mpr ⟨(fx t - fx s, ry t - ry s), ?_, by omega, by omega⟩
      rcases hx with h1 | h1 | h1 | h1 <;> rcases hy with h2 | h2 | h2 | h2 <;>
        rw [h1, h2] at ⊢ <;> first | decide | (exfalso; omega)
  · constructor
    · intro h
      have h2 : t ∈ rays b s bishopD := h
      obtain ⟨d, hd, k, hk1, hfx, hry, hclear⟩ := (mem_rays_iff b s t bishopD bishopD_sub_queenD).mp h
      refine ⟨?_, fun _ => hclear⟩
      simp only [geomAttack, diagLine, aligned, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
        Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      simp only [bishopD, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> dsimp only at hfx hry <;>
        exact ⟨⟨sq_ne_of_coords s t (Or.inl (by omega)), Or.inr (by omega)⟩, by omega, by omega⟩
    · rintro ⟨hg, hclear⟩
      show t ∈ rays b s bishopD
      simp only [geomAttack, diagLine, aligned, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
        Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hg
      obtain ⟨⟨hne_st, hor⟩, hnfx, hnry⟩ := hg
      rcases hor with hfr | hnat
      · rcases hfr with h1 | h1
        · exact absurd h1 hnfx
        · exact absurd h1 hnry
      · have hc := hclear (show isSlider Kind.bishop = true from by decide)
        have hfx0 : fx t - fx s ≠ 0 := fun h2 => hnfx (by omega)
        have hry0 : ry t - ry s ≠ 0 := fun h2 => hnry (by omega)
        have habs : (fx t - fx s).natAbs = (ry t - ry s).natAbs := by omega
        have ih1 := int_mul_isig (fx t - fx s)
        have ih2 := int_mul_isig (ry t - ry s)
        refine (mem_rays_iff b s t bishopD bishopD_sub_queenD).mpr
          ⟨(isig (fx t - fx s), isig (ry t - ry s)), bishopD_isig _ _, (fx t - fx s).natAbs,
            by omega, by dsimp only; omega, by dsimp only; rw [habs]; omega, hc⟩
  · constructor
    · intro h
      have h2 : t ∈ rays b s rookD := h
      obtain ⟨d, hd, k, hk1, hfx, hry, hclear⟩ := (mem_rays_iff b s t rookD rookD_sub_queenD).mp h
      refine ⟨?_, fun _ => hclear⟩
      simp only [geomAttack, orthLine, aligned, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
        Bool.or_eq_true]
      simp only [rookD, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> dsimp only at hfx hry
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact sq_ne_of_coords s t (Or.inl (by omega))
        · exact Or.inl (Or.inr (by omega))
        · omega
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact sq_ne_of_coords s t (Or.inl (by omega))
        · exact Or.inl (Or.inr (by omega))
        · omega
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact sq_ne_of_coords s t (Or.inr (by omega))
        · exact Or.inl (Or.inl (by omega))
        · omega
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact sq_ne_of_coords s t (Or.inr (by omega))
        · exact Or.inl (Or.inl (by omega))
        · omega
    · rintro ⟨hg, hclear⟩
      show t ∈ rays b s rookD
      simp only [geomAttack, orthLine, aligned, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
        Bool.or_eq_true] at hg
      obtain ⟨⟨hne_st, hor⟩, hfork⟩ := hg
      have hc := hclear (show isSlider Kind.rook = true from by decide)
      rcases hfork with hfxe | hrye
      · have hry0 : ry t - ry s ≠ 0 := fun h2 => hne_st (sq_eq_of_coords s t hfxe (by omega))
        have ih2 := int_mul_isig (ry t - ry s)
        exact (mem_rays_iff b s t rookD rookD_sub_queenD).mpr
          ⟨((0:Int), isig (ry t - ry s)), rookD_isig_r _, (ry t - ry s).natAbs,
            by omega, by (dsimp only; omega), by (dsimp only; omega), hc⟩
      · have hfx0 : fx t - fx s ≠ 0 := fun h2 => hne_st (sq_eq_of_coords s t (by omega) hrye)
        have ih1 := int_mul_isig (fx t - fx s)
        exact (mem_rays_iff b s t rookD rookD_sub_queenD).mpr
          ⟨(isig (fx t - fx s), (0:Int)), rookD_isig_l _, (fx t - fx s).natAbs,
            by omega, by (dsimp only; omega), by (dsimp only; omega), hc⟩
  · constructor
    · intro h
      have h2 : t ∈ rays b s queenD := h
      obtain ⟨d, hd, k, hk1, hfx, hry, hclear⟩ := (mem_rays_iff b s t queenD (fun d hd => hd)).mp h
      refine ⟨?_, fun _ => hclear⟩
      simp only [geomAttack, aligned, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, Bool.or_eq_true]
      rcases queenD_decomp d hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only at hfx hry
      · exact ⟨sq_ne_of_coords s t (Or.inl (by omega)), Or.inl (Or.inr (by omega))⟩
      · exact ⟨sq_ne_of_coords s t (Or.inl (by omega)), Or.inl (Or.inr (by omega))⟩
      · exact ⟨sq_ne_of_coords s t (Or.inr (by omega)), Or.inl (Or.inl (by omega))⟩
      · exact ⟨sq_ne_of_coords s t (Or.inr (by omega)), Or.inl (Or.inl (by omega))⟩
      · exact ⟨sq_ne_of_coords s t (Or.inl (by omega)), Or.inr (by omega)⟩
      · exact ⟨sq_ne_of_coords s t (Or.inl (by omega)), Or.inr (by omega)⟩
      · exact ⟨sq_ne_of_coords s t (Or.inl (by omega)), Or.inr (by omega)⟩
      · exact ⟨sq_ne_of_coords s t (Or.inl (by omega)), Or.inr (by omega)⟩
    · rintro ⟨hg, hclear⟩
      show t ∈ rays b s queenD
      simp only [geomAttack, aligned, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, Bool.or_eq_true] at hg
      obtain ⟨hne_st, hor⟩ := hg
      have hc := hclear (show isSlider Kind.queen = true from by decide)
      rcases hor with hfr | hnat
      · rcases hfr with hfxe | hrye
        · have hry0 : ry t - ry s ≠ 0 := fun h2 => hne_st (sq_eq_of_coords s t hfxe (by omega))
          have ih2 := int_mul_isig (ry t - ry s)
          exact (mem_rays_iff b s t queenD (fun d hd => hd)).mpr
            ⟨((0:Int), isig (ry t - ry s)), rookD_sub_queenD _ (rookD_isig_r _),
              (ry t - ry s).natAbs, by omega, by (dsimp only; omega), by (dsimp only; omega), hc⟩
        · have hfx0 : fx t - fx s ≠ 0 := fun h2 => hne_st (sq_eq_of_coords s t (by omega) hrye)
          have ih1 := int_mul_isig (fx t - fx s)
          exact (mem_rays_iff b s t queenD (fun d hd => hd)).mpr
            ⟨(isig (fx t - fx s), (0:Int)), rookD_sub_queenD _ (rookD_isig_l _),
              (fx t - fx s).natAbs, by omega, by (dsimp only; omega), by (dsimp only; omega), hc⟩
      · have hfx0 : fx t - fx s ≠ 0 := by
          intro h2
          apply hne_st
          apply sq_eq_of_coords <;> omega
        have hry0 : ry t - ry s ≠ 0 := by
          intro h2
          apply hne_st
          apply sq_eq_of_coords <;> omega
        have habs : (fx t - fx s).natAbs = (ry t - ry s).natAbs := by omega
        have ih1 := int_mul_isig (fx t - fx s)
        have ih2 := int_mul_isig (ry t - ry s)
        exact (mem_rays_iff b s t queenD (fun d hd => hd)).mpr
          ⟨(isig (fx t - fx s), isig (ry t - ry s)),
            bishopD_sub_queenD _ (bishopD_isig _ _), (fx t - fx s).natAbs,
            by omega, by dsimp only; omega, by dsimp only; rw [habs]; omega, hc⟩
  · constructor
    · intro h
      have h2 : t ∈ steps s queenD := h
      obtain ⟨d, hd, hfx, hry⟩ := (mem_steps s t _).mp h2
      rcases queenD_decomp d hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only at hfx hry
      all_goals refine ⟨?_, fun hi => absurd hi (show isSlider Kind.king ≠ true from by decide)⟩
      all_goals simp only [geomAttack, beq_iff_eq]
      all_goals simp only [kdist] <;> omega
    · rintro ⟨hg, -⟩
      show t ∈ steps s queenD
      simp only [geomAttack, beq_iff_eq] at hg
      simp only [kdist] at hg
      have hx : fx t - fx s = 0 ∨ fx t - fx s = 1 ∨ fx t - fx s = -1 := by omega
      have hy : ry t - ry s = 0 ∨ ry t - ry s = 1 ∨ ry t - ry s = -1 := by omega
      have hne : ¬(fx t - fx s = 0 ∧ ry t - ry s = 0) := fun ⟨h1, h2⟩ => by omega
      exact (mem_steps s t queenD).mpr
        ⟨(fx t - fx s, ry t - ry s), mem_queenD_of _ _ hx hy hne, by omega, by omega⟩

theorem attacks_ne (b : Board) (s t : Sq) (q : Piece) (h : t ∈ attacks b s q) : t ≠ s := by
  intro hts
  subst hts
  obtain ⟨c, k⟩ := q
  rw [mem_attacks_iff] at h
  obtain ⟨h1, -⟩ := h
  cases k
  case pawn =>
    simp only [geomAttack, Bool.and_eq_true, beq_iff_eq] at h1
    cases c <;> simp only [Color.fwd] at h1 <;> omega
  case knight => simp [geomAttack, knightJump] at h1
  case king => simp [geomAttack, kdist] at h1
  case bishop => simp [geomAttack, diagLine, aligned] at h1
  case rook => simp [geomAttack, orthLine, aligned] at h1
  case queen => simp [geomAttack, aligned] at h1

theorem attacks_congr (b b' : Board) (s t : Sq) (q : Piece) (h : ∀ z, inSeg s t z = true → b z = b' z) :
    t ∈ attacks b s q ↔ t ∈ attacks b' s q := by
  have hcp : clearPath b s t ↔ clearPath b' s t := by
    constructor
    · intro hb z hz
      have hz' := hb z hz
      rw [h z hz] at hz'
      exact hz'
    · intro hb z hz
      have hz' := hb z hz
      rw [← h z hz] at hz'
      exact hz'
  rw [mem_attacks_iff, mem_attacks_iff]
  exact and_congr Iff.rfl (imp_congr Iff.rfl hcp)

theorem attacked_iff (b : Board) (s : Sq) (c : Color) :
    attacked b s c = true ↔ ∃ t q, b t = some q ∧ q.color = c ∧ s ∈ attacks b t q := by
  unfold attacked
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, -, ht⟩
    revert ht
    cases hm : b t with
    | none => intro ht; simp at ht
    | some q =>
      intro ht
      simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at ht
      exact ⟨t, q, hm, ht.1, ht.2⟩
  · rintro ⟨t, q, hm, hc, hmem⟩
    refine ⟨t, mem_allSq t, ?_⟩
    rw [hm]
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
    exact ⟨hc, hmem⟩

theorem inCheck_iff (p : Pos) (c : Color) :
    inCheck p c = true ↔ ∃ k, kingAt p c k ∧ attacked p.board k c.opp = true := by
  unfold inCheck
  rw [List.any_eq_true]
  constructor
  · rintro ⟨k, -, hk⟩
    rw [Bool.and_eq_true, beq_iff_eq] at hk
    exact ⟨k, hk.1, hk.2⟩
  · rintro ⟨k, hk1, hk2⟩
    exact ⟨k, mem_allSq k, Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr hk1, hk2⟩⟩

theorem king_attack_adjacent (b : Board) (s t : Sq) (c : Color) (h : t ∈ attacks b s ⟨c, .king⟩) :
    kdist s t = 1 := by
  rw [mem_attacks_iff] at h
  obtain ⟨h1, -⟩ := h
  simp only [geomAttack] at h1
  exact beq_iff_eq.mp h1

theorem mem_checkers (p : Pos) (k t : Sq) :
    t ∈ checkers p k ↔ ∃ q, p.board t = some q ∧ q.color = p.turn.opp ∧ k ∈ attacks p.board t q := by
  unfold checkers
  rw [List.mem_filter]
  constructor
  · rintro ⟨-, ht⟩
    revert ht
    cases hm : p.board t with
    | none => intro ht; simp at ht
    | some q =>
      intro ht
      simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at ht
      exact ⟨q, rfl, ht.1, ht.2⟩
  · rintro ⟨q, hm, hc, hmem⟩
    refine ⟨mem_allSq t, ?_⟩
    rw [hm]
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
    exact ⟨hc, hmem⟩

theorem inCheck_iff_checkers (p : Pos) (k : Sq) (hk : kingAt p p.turn k)
    (huniq : ∀ s, kingAt p p.turn s → s = k) :
    inCheck p p.turn = true ↔ checkers p k ≠ [] := by
  rw [inCheck_iff]
  constructor
  · rintro ⟨k', hk', hatt⟩
    have heq : k' = k := huniq k' hk'
    rw [heq] at hatt
    rw [attacked_iff] at hatt
    obtain ⟨t, q, hbt, hc, hmem⟩ := hatt
    have ht : t ∈ checkers p k := (mem_checkers p k t).mpr ⟨q, hbt, hc, hmem⟩
    intro hnil
    rw [hnil] at ht
    simp at ht
  · intro hne
    have hex : ∃ t, t ∈ checkers p k := by
      match hl : checkers p k with
      | [] => exact absurd hl hne
      | t :: _ => exact ⟨t, by simp⟩
    obtain ⟨t, ht⟩ := hex
    rw [mem_checkers] at ht
    obtain ⟨q, hbt, hc, hmem⟩ := ht
    exact ⟨k, hk, (attacked_iff p.board k p.turn.opp).mpr ⟨t, q, hbt, hc, hmem⟩⟩

theorem slider_line (b : Board) (s t : Sq) (q : Piece) (hs : isSlider q.kind = true) (h : t ∈ attacks b s q) :
    aligned s t = true := by
  rw [mem_attacks_iff] at h
  obtain ⟨c, k⟩ := q
  cases k <;> simp [isSlider] at hs
  case bishop =>
    simp only [geomAttack, diagLine, Bool.and_eq_true] at h
    exact h.1.1
  case rook =>
    simp only [geomAttack, orthLine, Bool.and_eq_true] at h
    exact h.1.1
  case queen =>
    simp only [geomAttack] at h
    exact h.1

theorem pawn_attack_geom (b : Board) (s t : Sq) (c : Color) (h : t ∈ attacks b s ⟨c, .pawn⟩) :
    ry t = ry s + c.fwd ∧ (fx t - fx s).natAbs = 1 := by
  rw [mem_attacks_iff] at h
  obtain ⟨h1, -⟩ := h
  simp only [geomAttack, Bool.and_eq_true, beq_iff_eq] at h1
  exact h1

end Chess.C364
