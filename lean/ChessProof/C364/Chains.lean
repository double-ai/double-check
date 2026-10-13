import ChessProof.C364.KingPly

namespace Chess.C364

open Chess

theorem after_nil (p : Pos) : after p [] = p := rfl

theorem after_cons (p : Pos) (m : Move) (ms : List Move) : after p (m :: ms) = after (play p m) ms := rfl

theorem after_append (p : Pos) (ms₁ ms₂ : List Move) : after p (ms₁ ++ ms₂) = after (after p ms₁) ms₂ := by
  simp [after, List.foldl_append]

theorem kf_append (p : Pos) (ms₁ ms₂ : List Move) :
    KFChain p (ms₁ ++ ms₂) ↔ KFChain p ms₁ ∧ KFChain (after p ms₁) ms₂ := by
  induction ms₁ generalizing p with
  | nil => simp [KFChain, after]
  | cons m ms ih => simp only [List.cons_append, KFChain, ih, after_cons, and_assoc]

theorem caps_append (p : Pos) (ms₁ ms₂ : List Move) :
    caps p (ms₁ ++ ms₂) = caps p ms₁ + caps (after p ms₁) ms₂ := by
  induction ms₁ generalizing p with
  | nil => simp [caps, after]
  | cons m ms ih => simp only [List.cons_append, caps, ih, after_cons]; omega

theorem c0_after_kf (p : Pos) (ms : List Move) (hc : C0 p) (h : KFChain p ms) : C0 (after p ms) := by
  induction ms generalizing p with
  | nil => exact hc
  | cons m ms ih =>
    obtain ⟨hm, -, -, h'⟩ := h
    exact ih (play p m) (c0_play p m hc hm) h'

theorem kf_take (p : Pos) (ms : List Move) (k : Nat) (h : KFChain p ms) :
    KFChain p (ms.take k) ∧ caps p (ms.take k) ≤ caps p ms := by
  have e := List.take_append_drop k ms
  have h' : KFChain p (ms.take k ++ ms.drop k) := by rw [e]; exact h
  have h2 := (kf_append p (ms.take k) (ms.drop k)).mp h'
  refine ⟨h2.1, ?_⟩
  have := caps_append p (ms.take k) (ms.drop k)
  rw [e] at this
  omega

theorem kf_split_capture (p : Pos) (ms : List Move) (j : Nat) (h : KFChain p ms) (hj : j < caps p ms) :
    ∃ ms₁ x ms₂, ms = ms₁ ++ x :: ms₂ ∧ caps p ms₁ = j ∧ isCapture (after p ms₁) x = true := by
  induction ms generalizing p j with
  | nil => simp [caps] at hj
  | cons m ms ih =>
    obtain ⟨hm, hg, hkm, h'⟩ := h
    cases hc : isCapture p m with
    | true =>
      cases j with
      | zero => exact ⟨[], m, ms, rfl, rfl, hc⟩
      | succ j' =>
        have hj' : j' < caps (play p m) ms := by
          have e : caps p (m :: ms) = 1 + caps (play p m) ms := by simp [caps, hc]
          omega
        obtain ⟨ms₁, x, ms₂, rfl, hc₁, hx⟩ := ih (play p m) j' h' hj'
        refine ⟨m :: ms₁, x, ms₂, rfl, ?_, hx⟩
        have e : caps p (m :: ms₁) = 1 + caps (play p m) ms₁ := by simp [caps, hc]
        omega
    | false =>
      have hj' : j < caps (play p m) ms := by
        have e : caps p (m :: ms) = caps (play p m) ms := by simp [caps, hc]
        omega
      obtain ⟨ms₁, x, ms₂, rfl, hc₁, hx⟩ := ih (play p m) j h' hj'
      refine ⟨m :: ms₁, x, ms₂, rfl, ?_, hx⟩
      have e : caps p (m :: ms₁) = caps (play p m) ms₁ := by simp [caps, hc]
      omega

theorem lemmaB (Bf : Nat → Nat) (m : Nat) (hB : ∀ k, k ≤ m → BoundB k (Bf k)) (q r : Nat) (hr : r ≤ m) :
    ∀ p ms, C0 p → KFChain p ms → caps p ms = q * (m + 1) + r → ms.length ≤ q * (Bf m + 1) + Bf r := by
  induction q with
  | zero =>
    intro p ms hc hk hcap
    simpa using hB r hr p ms hc hk (by omega)
  | succ q ih =>
    intro p ms hc hk hcap
    obtain ⟨ms₁, x, ms₂, rfl, hc₁, hx⟩ := kf_split_capture p ms m hk (by rw [hcap, Nat.succ_mul]; omega)
    have hkf := (kf_append p ms₁ (x :: ms₂)).mp hk
    obtain ⟨hk₁, hxl, -, -, hk₂⟩ := hkf
    have hca := caps_append p ms₁ (x :: ms₂)
    simp only [caps, hx, ↓reduceIte] at hca
    have hl₁ := hB m (Nat.le_refl _) p ms₁ hc hk₁ (by omega)
    have hc' := c0_play _ x (c0_after_kf p ms₁ hc hk₁) hxl
    have hl₂ := ih _ ms₂ hc' hk₂ (by rw [Nat.succ_mul] at hcap; omega)
    simp only [List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem f_mono (a b : Nat) (h : a ≤ b) : f a ≤ f b := by
  unfold f
  split <;> split <;> omega

theorem f_pair : ∀ x y, x + y ≤ 29 → f x + 1 + f y ≤ 364 := by
  intro x y h
  have hx : x < 30 := by omega
  have hy : y < 30 := by omega
  revert h
  revert x
  revert y
  decide

theorem f_single : ∀ x, x ≤ 29 → f x ≤ 364 := by decide

theorem chain_le_f (h0 : BoundB 0 19) (h1 : BoundB 1 22) (p : Pos) (ms : List Move) (hc : C0 p)
    (h : KFChain p ms) : ms.length ≤ f (caps p ms) := by
  have hB : ∀ k, k ≤ 1 → BoundB k (if k = 0 then 19 else 22) := by
    intro k hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · exact h0
    · exact h1
  have hr : caps p ms % 2 ≤ 1 := by omega
  have := lemmaB (fun k => if k = 0 then 19 else 22) 1 hB (caps p ms / 2) (caps p ms % 2) hr p ms hc h
    (by omega)
  unfold f
  split <;> split at this <;> simp_all <;> omega

theorem kf_of_checkSeq (p : Pos) (ms : List Move) (hs : IsCheckSeq p ms) (hk : kingPlies p ms = 0) :
    KFChain p ms := by
  induction ms generalizing p with
  | nil => trivial
  | cons m ms ih =>
    obtain ⟨hm, hg, hs'⟩ := hs
    cases hkm : isKingMove p m with
    | true => simp [kingPlies, hkm] at hk
    | false =>
      simp [kingPlies, hkm] at hk
      exact ⟨hm, hg, hkm, ih (play p m) hs' hk⟩

theorem checkSeq_split (p : Pos) (ms : List Move) (hs : IsCheckSeq p ms) (hk : kingPlies p ms = 1) :
    ∃ ms₁ m ms₂, ms = ms₁ ++ m :: ms₂ ∧ KFChain p ms₁ ∧ m ∈ legalMoves (after p ms₁) ∧
      isKingMove (after p ms₁) m = true ∧ KFChain (play (after p ms₁) m) ms₂ := by
  induction ms generalizing p with
  | nil => simp [kingPlies] at hk
  | cons m ms ih =>
    obtain ⟨hm, hg, hs'⟩ := hs
    cases hkm : isKingMove p m with
    | true =>
      have hk0 : kingPlies (play p m) ms = 0 := by
        have e : kingPlies p (m :: ms) = 1 + kingPlies (play p m) ms := by simp [kingPlies, hkm]
        omega
      exact ⟨[], m, ms, rfl, trivial, hm, hkm, kf_of_checkSeq _ _ hs' hk0⟩
    | false =>
      have hk0 : kingPlies (play p m) ms = 1 := by
        have e : kingPlies p (m :: ms) = kingPlies (play p m) ms := by simp [kingPlies, hkm]
        omega
      obtain ⟨ms₁, x, ms₂, rfl, hk₁, hx, hxk, hk₂⟩ := ih (play p m) hs' hk0
      exact ⟨m :: ms₁, x, ms₂, rfl, ⟨hm, hg, hkm, hk₁⟩, hx, hxk, hk₂⟩

theorem caps_checkSeq (p : Pos) (ms : List Move) (hc : C0 p) (hs : IsCheckSeq p ms) :
    caps p ms + nonKing (after p ms) = nonKing p := by
  induction ms generalizing p with
  | nil =>
    show 0 + nonKing p = nonKing p
    exact Nat.zero_add _
  | cons m ms ih =>
    obtain ⟨hm, hg, hs'⟩ := hs
    have e1 := nonKing_play p m hc hm
    have e2 := ih (play p m) (c0_play p m hc hm) hs'
    simp only [caps, after_cons]
    omega

theorem caps_le_29 (p : Pos) (ms : List Move) (hr : Reachable p) (hs : IsCheckSeq p ms) (hne : ms ≠ []) :
    caps p ms ≤ 29 := by
  have hc := reachable_c0 p hr
  have e := caps_checkSeq p ms hc hs
  have h30 := nonKing_reachable p hr
  have hlen : 1 ≤ ms.length := by
    cases ms with
    | nil => exact absurd rfl hne
    | cons => simp
  have hchk := checkSeq_inCheck p ms hs ms.length hlen (Nat.le_refl _)
  have hreach := checkSeq_reachable p ms hr hs ms.length (Nat.le_refl _)
  simp only [posAt, List.take_length] at hchk hreach
  have h1 := nonKing_pos_of_check (after p ms) (reachable_c0 _ hreach) hchk
  omega

theorem checks_le_364_of_B (h0 : BoundB 0 19) (h1 : BoundB 1 22) :
    ∀ (p : Pos) (ms : List Move), Reachable p → IsCheckSeq p ms → ms.length ≤ 364 := by
  intro p ms hr hs
  by_cases hne : ms = []
  · simp [hne]
  have hC := caps_le_29 p ms hr hs hne
  have hc0 := reachable_c0 p hr
  have hK := theoremK' p ms hr hs
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hK with hk | hk
  · have hkf := kf_of_checkSeq p ms hs hk
    have := chain_le_f h0 h1 p ms hc0 hkf
    have := f_mono _ _ hC
    have := f_single 29 (by decide)
    omega
  · obtain ⟨ms₁, m, ms₂, rfl, hk₁, hm, _, hk₂⟩ := checkSeq_split p ms hs hk
    have hc1 := c0_after_kf p ms₁ hc0 hk₁
    have hc2 := c0_play _ m hc1 hm
    have hl₁ := chain_le_f h0 h1 p ms₁ hc0 hk₁
    have hl₂ := chain_le_f h0 h1 _ ms₂ hc2 hk₂
    have hcaps := caps_append p ms₁ (m :: ms₂)
    simp only [caps] at hcaps
    have hsum : caps p ms₁ + caps (play (after p ms₁) m) ms₂ ≤ 29 := by
      split at hcaps <;> omega
    have := f_pair _ _ hsum
    simp only [List.length_append, List.length_cons]
    omega

end Chess.C364
