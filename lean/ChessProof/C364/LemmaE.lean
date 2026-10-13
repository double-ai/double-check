import ChessProof.C364.C0

namespace Chess.C364

open Chess

theorem lemmaE_inCheck (p : Pos) (m : Move) (h : givesCheck p m = true) :
    inCheck (play p m) (play p m).turn = true := h

theorem inSeg_ne {a b z : Sq} (h : inSeg a b z = true) : z ≠ a ∧ z ≠ b := by
  simp only [inSeg, onLine, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
  exact ⟨h.1.1.2, h.1.2⟩

theorem aligned_ab_of_inSeg {a b z : Sq} (h : inSeg a b z = true) : aligned a b = true := by
  simp only [inSeg, onLine, Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem kdist_pos (a b : Sq) (h : a ≠ b) : 1 ≤ kdist a b := by
  have hne := sq_ne_coords a b h
  by_cases hf : fx a = fx b
  · have hr : ry a ≠ ry b := fun hh => hne ⟨hf, hh⟩
    unfold kdist
    omega
  · unfold kdist
    omega

theorem opp_ne_self (c : Color) : ¬c = c.opp := by cases c <;> decide

theorem color_fwd_cases (c : Color) :
    c.fwd = 1 ∧ c.opp.fwd = -1 ∨ c.fwd = -1 ∧ c.opp.fwd = 1 := by
  cases c <;> simp [Color.fwd, Color.opp]

theorem checker_seg_empty (p : Pos) (k c z : Sq) (hc : c ∈ checkers p k) (hz : inSeg c k z = true) :
    p.board z = none := by
  obtain ⟨q, hq, -, hatt⟩ := (mem_checkers p k c).mp hc
  obtain ⟨hg, hclear⟩ := (mem_attacks_iff p.board c k q).mp hatt
  have hzc : z ≠ c := (inSeg_ne hz).1
  have hkd : kdist c z < kdist c k := (inSeg_aligned c k z hz).2.2
  have hzc1 : 1 ≤ kdist c z := kdist_pos c z (fun h => hzc h.symm)
  have hal : aligned c k = true := aligned_ab_of_inSeg hz
  obtain ⟨cc, kk⟩ := q
  cases kk with
  | pawn =>
    exfalso
    simp only [geomAttack, Bool.and_eq_true, beq_iff_eq] at hg
    obtain ⟨hry, hfx⟩ := hg
    cases cc with
    | white =>
      simp only [Color.fwd] at hry
      have h1 : kdist c k = 1 := by
        unfold kdist
        omega
      omega
    | black =>
      simp only [Color.fwd] at hry
      have h1 : kdist c k = 1 := by
        unfold kdist
        omega
      omega
  | knight =>
    exfalso
    have hkj : knightJump c k = true := hg
    have hna := knightJump_not_aligned c k hkj
    rw [hal] at hna
    exact absurd hna (by decide)
  | king =>
    exfalso
    have h1 : kdist c k = 1 := beq_iff_eq.mp hg
    omega
  | bishop =>
    exact hclear (by show isSlider Kind.bishop = true; decide) z hz
  | rook =>
    exact hclear (by show isSlider Kind.rook = true; decide) z hz
  | queen =>
    exact hclear (by show isSlider Kind.queen = true; decide) z hz

theorem checker_blocked (p : Pos) (k a b : Sq) (ha : a ∈ checkers p k) (hb : b ∈ checkers p k)
    (hseg : inSeg a k b = true) : False := by
  obtain ⟨q, hq, -, -⟩ := (mem_checkers p k b).mp hb
  have hnone := checker_seg_empty p k a b ha hseg
  rw [hq] at hnone
  exact (Option.some_ne_none q) hnone

theorem checkers_two (p : Pos) (k : Sq) (h : 2 ≤ (checkers p k).length) :
    ∃ c₁ c₂, c₁ ∈ checkers p k ∧ c₂ ∈ checkers p k ∧ c₁ ≠ c₂ := by
  have hnd : (checkers p k).Nodup :=
    List.Nodup.sublist List.filter_sublist (List.nodup_finRange 64)
  cases hl : checkers p k with
  | nil =>
    rw [hl] at h
    simp at h
  | cons c₁ tail =>
    cases htl : tail with
    | nil =>
      rw [hl, htl] at h
      simp at h
    | cons c₂ rest =>
      rw [hl, htl] at hnd
      refine ⟨c₁, c₂, by simp, by simp, fun heq => ?_⟩
      rw [heq] at hnd
      exact (List.nodup_cons.mp hnd).1 List.mem_cons_self

theorem nonking_board_change (p : Pos) (m : Move) (hm : m ∈ legalMoves p) (hk : isKingMove p m = false)
    (s : Sq) (hs : s ≠ m.src) (hd : s ≠ m.dst) (he : epVictim p m ≠ some s) :
    (play p m).board s = p.board s := by
  have hcast : isCastle p m = false := by
    unfold isCastle
    rw [hk, Bool.false_and]
  exact play_board_other p m s hs hd he hcast

theorem checker_survives (p : Pos) (k c : Sq) (hc0 : C0 p) (hk : kingAt p p.turn k)
    (hc : c ∈ checkers p k) (m : Move) (hm : m ∈ legalMoves p) (hnk : isKingMove p m = false)
    (hd : m.dst ≠ c) (he : epVictim p m ≠ some c) (hs : inSeg c k m.dst = false) :
    inCheck (play p m) p.turn = true := by
  obtain ⟨q, hq, hcq, hatt⟩ := (mem_checkers p k c).mp hc
  have hkK : kingAt (play p m) p.turn k :=
    (kingAt_play_nonking p m hm hnk hc0.safe p.turn k).mpr hk
  obtain ⟨q', hq', hcq'⟩ := legal_src p m hm
  have hcs : c ≠ m.src := by
    intro hh
    rw [hh] at hq
    have hqq : q' = q := Option.some.inj (hq'.symm.trans hq)
    rw [← hqq] at hcq
    rw [hcq'] at hcq
    exact opp_ne_self p.turn hcq
  have hagree : ∀ z, inSeg c k z = true → p.board z = (play p m).board z := by
    intro z hzz
    have hznone : p.board z = none := checker_seg_empty p k c z hc hzz
    have hzd : z ≠ m.dst := by
      intro hh
      rw [hh] at hzz
      rw [hzz] at hs
      exact absurd hs (by decide)
    have hzs : z ≠ m.src := by
      intro hh
      rw [hh, hq'] at hznone
      exact (Option.some_ne_none q') hznone
    have hze : epVictim p m ≠ some z := by
      intro hhv
      obtain ⟨-, -, hbv, -⟩ := epVictim_spec p m z hm hhv
      rw [hbv] at hznone
      exact (Option.some_ne_none _) hznone
    exact (nonking_board_change p m hm hnk z hzs hzd hze).symm
  have hatt2 : k ∈ attacks (play p m).board c q := (attacks_congr p.board _ c k q hagree).mp hatt
  have hbc : (play p m).board c = some q := by
    rw [nonking_board_change p m hm hnk c hcs (Ne.symm hd) he, hq]
  have hattk : attacked (play p m).board k p.turn.opp = true :=
    (attacked_iff (play p m).board k p.turn.opp).mpr ⟨c, q, hbc, hcq, hatt2⟩
  exact (inCheck_iff (play p m) p.turn).mpr ⟨k, hkK, hattk⟩

theorem checker_removed_or_blocked (p : Pos) (k c : Sq) (hc0 : C0 p) (hk : kingAt p p.turn k)
    (hc : c ∈ checkers p k) (m : Move) (hm : m ∈ legalMoves p) (hnk : isKingMove p m = false) :
    m.dst = c ∨ epVictim p m = some c ∨ inSeg c k m.dst = true := by
  by_cases hd : m.dst = c
  · exact Or.inl hd
  by_cases he : epVictim p m = some c
  · exact Or.inr (Or.inl he)
  by_cases hsg : inSeg c k m.dst = true
  · exact Or.inr (Or.inr hsg)
  have hsg' : inSeg c k m.dst = false := Bool.not_eq_true _ |>.mp hsg
  have hchk := checker_survives p k c hc0 hk hc m hm hnk hd he hsg'
  rw [legal_safe p m hm] at hchk
  exact absurd hchk (by decide)

theorem ep_landing_knight (p : Pos) (k v : Sq) (hc0 : C0 p) (hk : kingAt p p.turn k) (m : Move)
    (hm : m ∈ legalMoves p) (hv : epVictim p m = some v) (hvc : v ∈ checkers p k) :
    knightJump m.dst k = true := by
  obtain ⟨-, -, hbv, hfxv, hryv, hsrcp⟩ := epVictim_spec p m v hm hv
  obtain ⟨qv, hqv, -, hatt⟩ := (mem_checkers p k v).mp hvc
  have hqp : qv = ⟨p.turn.opp, .pawn⟩ := Option.some.inj (hqv.symm.trans hbv)
  obtain ⟨hry1, hfx1⟩ := pawn_attack_geom p.board v k p.turn.opp (hqp ▸ hatt)
  have hki : isKingMove p m = false := isKingMove_false_of_ep p m hm v hv
  have hfiles : (m.src.file != m.dst.file) = true := by
    unfold epVictim at hv
    split at hv
    · rename_i hcond
      simp only [Bool.and_eq_true] at hcond
      exact hcond.1.2
    · contradiction
  have hfxne : fx m.src ≠ fx m.dst := by
    intro hh
    exact bne_iff_ne.mp hfiles (Int.ofNat_inj.mp hh)
  obtain ⟨q', hq', -, hmem⟩ := legal_nonking_mem p m hm hki
  have hqe : q' = ⟨p.turn, .pawn⟩ := Option.some.inj (hq'.symm.trans hsrcp)
  subst hqe
  have hmem2 : m ∈ pawnMoves p m.src p.turn := hmem
  obtain ⟨-, hdisj, -⟩ := pawnMoves_cases p m.src p.turn m hmem2
  rcases hdisj with hd1 | hd2 | hd3
  · exact absurd hd1.1 (Ne.symm hfxne)
  · exact absurd hd2.1 (Ne.symm hfxne)
  · obtain ⟨hatt2, -⟩ := hd3
    obtain ⟨hry2, -⟩ := pawn_attack_geom p.board m.src m.dst p.turn hatt2
    have key : (fx m.dst - fx k).natAbs = 1 ∧ (ry m.dst - ry k).natAbs = 2 := by
      have hfc := color_fwd_cases p.turn
      omega
    unfold knightJump
    rw [key.1, key.2]
    decide

theorem lemmaE_double (p : Pos) (k : Sq) (hc0 : C0 p) (hk : kingAt p p.turn k)
    (h2 : 2 ≤ (checkers p k).length) (m : Move) (hm : m ∈ legalMoves p) : isKingMove p m = true := by
  cases hmk : isKingMove p m with
  | true => rfl
  | false =>
  exfalso
  obtain ⟨c₁, c₂, hm1, hm2, hne⟩ := checkers_two p k h2
  have h1 := checker_removed_or_blocked p k c₁ hc0 hk hm1 m hm hmk
  have h2' := checker_removed_or_blocked p k c₂ hc0 hk hm2 m hm hmk
  rcases h1 with hd1 | he1 | hs1 <;> rcases h2' with hd2 | he2 | hs2
  · exact hne (hd1.symm.trans hd2)
  · obtain ⟨-, hbnone, -⟩ := epVictim_spec p m c₂ hm he2
    obtain ⟨q, hq, -, -⟩ := (mem_checkers p k c₁).mp hm1
    rw [← hd1] at hq
    rw [hbnone] at hq
    exact (Option.some_ne_none q) hq.symm
  · rw [hd1] at hs2
    exact checker_blocked p k c₂ c₁ hm2 hm1 hs2
  · obtain ⟨-, hbnone, -⟩ := epVictim_spec p m c₁ hm he1
    obtain ⟨q, hq, -, -⟩ := (mem_checkers p k c₂).mp hm2
    rw [← hd2] at hq
    rw [hbnone] at hq
    exact (Option.some_ne_none q) hq.symm
  · exact hne (Option.some.inj (he1.symm.trans he2))
  · have hkj := ep_landing_knight p k c₁ hc0 hk m hm he1 hm1
    have hna := knightJump_not_aligned m.dst k hkj
    have hal2 : aligned m.dst k = true := (inSeg_aligned c₂ k m.dst hs2).2.1
    rw [hal2] at hna
    exact absurd hna (by decide)
  · rw [hd2] at hs1
    exact checker_blocked p k c₁ c₂ hm1 hm2 hs1
  · have hkj := ep_landing_knight p k c₂ hc0 hk m hm he2 hm2
    have hna := knightJump_not_aligned m.dst k hkj
    have hal1 : aligned m.dst k = true := (inSeg_aligned c₁ k m.dst hs1).2.1
    rw [hal1] at hna
    exact absurd hna (by decide)
  · rcases seg_disjoint_of_two_lines k c₁ c₂ m.dst hs1 hs2 hne with h | h
    · exact checker_blocked p k c₁ c₂ hm1 hm2 h
    · exact checker_blocked p k c₂ c₁ hm2 hm1 h

theorem lemmaE_single (p : Pos) (k c : Sq) (hc0 : C0 p) (hk : kingAt p p.turn k)
    (h1 : checkers p k = [c]) (m : Move) (hm : m ∈ legalMoves p) (hnk : isKingMove p m = false) :
    m.dst = c ∨ epVictim p m = some c ∨ inSeg c k m.dst = true :=
  checker_removed_or_blocked p k c hc0 hk (by rw [h1]; simp) m hm hnk

theorem checkers_le_one_of_nonking (p : Pos) (k : Sq) (hc0 : C0 p) (hk : kingAt p p.turn k) (m : Move)
    (hm : m ∈ legalMoves p) (hnk : isKingMove p m = false) : (checkers p k).length ≤ 1 := by
  by_cases hle : (checkers p k).length ≤ 1
  · exact hle
  have h2 : 2 ≤ (checkers p k).length := by omega
  have hking := lemmaE_double p k hc0 hk h2 m hm
  rw [hking] at hnk
  exact absurd hnk (by decide)

end Chess.C364
