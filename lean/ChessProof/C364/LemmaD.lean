import ChessProof.C364.LemmaE

namespace Chess.C364

open Chess

theorem king_board_change (p : Pos) (m : Move) (hm : m ∈ legalMoves p) (hk : isKingMove p m = true)
    (hc : isCastle p m = false) (s : Sq) (hs : s ≠ m.src) (hd : s ≠ m.dst) :
    (play p m).board s = p.board s := by
  apply play_board_other p m s hs hd _ hc
  intro hev
  obtain ⟨-, -, -, -, -, hsrcp⟩ := epVictim_spec p m s hm hev
  have hksrc : p.board m.src = some ⟨p.turn, .king⟩ := kingMove_src p m hm hk
  rw [hksrc] at hsrcp
  simp only [Option.some.injEq, Piece.mk.injEq] at hsrcp
  exact absurd hsrcp.2 (by decide)

theorem lemmaD_checker (p : Pos) (m : Move) (e : Sq) (hc0 : C0 p) (hm : m ∈ legalMoves p)
    (hk : isKingMove p m = true) (hc : isCastle p m = false) (hg : givesCheck p m = true)
    (he : kingAt p p.turn.opp e) :
    ∃ S q, S ≠ m.src ∧ S ≠ m.dst ∧ p.board S = some q ∧ q.color = p.turn ∧ q.kind ≠ .king ∧
      e ∈ attacks (play p m).board S q := by
  have hsd : m.src ≠ m.dst := legal_src_ne_dst p m hm
  have hksrc : p.board m.src = some ⟨p.turn, .king⟩ := kingMove_src p m hm hk
  have hpr : m.promo = none := kingMove_promo p m hm hk
  have hnes : e ≠ m.src := by
    intro hh
    rw [hh] at he
    have he2 : p.board m.src = some ⟨p.turn.opp, .king⟩ := he
    rw [hksrc] at he2
    have hcc : p.turn = p.turn.opp := congrArg Piece.color (Option.some.inj he2)
    have hone : ∀ c : Color, c ≠ c.opp := fun c => by cases c <;> decide
    exact absurd hcc (hone p.turn)
  have he' : (play p m).board e = some ⟨p.turn.opp, .king⟩ := king_stay p m hm hc0.safe _ _ he hnes
  have hbdst : (play p m).board m.dst = some ⟨p.turn, .king⟩ := by
    rw [play_board_dst, hpr, hksrc]
  have hic : inCheck (play p m) p.turn.opp = true := hg
  obtain ⟨k, hkk, hatt⟩ := (inCheck_iff (play p m) p.turn.opp).mp hic
  have hk_eq : k = e := by
    obtain ⟨hw, hb⟩ := c0_kings_play p m hc0 hm
    cases htu : p.turn with
    | white =>
      obtain ⟨B, hB⟩ := hb
      rw [htu] at hkk he'
      have h1 := (hB k).mp hkk
      have h2 := (hB e).mp he'
      exact h1.trans h2.symm
    | black =>
      obtain ⟨W, hW⟩ := hw
      rw [htu] at hkk he'
      have h1 := (hW k).mp hkk
      have h2 := (hW e).mp he'
      exact h1.trans h2.symm
  rw [hk_eq] at hatt
  have hatt' : attacked (play p m).board e p.turn = true := by
    rw [← Color.opp_opp p.turn]
    exact hatt
  obtain ⟨S, q, hbS, hqc, hattS⟩ := (attacked_iff _ _ _).mp hatt'
  have hqk : q.kind ≠ .king := by
    intro hkk2
    have hq' : q = ⟨p.turn, .king⟩ := by
      obtain ⟨c0, k0⟩ := q
      cases k0 with
      | king =>
        have hc0' : c0 = p.turn := hqc
        rw [hc0']
      | pawn => exact Kind.noConfusion hkk2
      | knight => exact Kind.noConfusion hkk2
      | bishop => exact Kind.noConfusion hkk2
      | rook => exact Kind.noConfusion hkk2
      | queen => exact Kind.noConfusion hkk2
    rw [hq'] at hbS hattS
    have hd1 : kdist S e = 1 := king_attack_adjacent _ _ _ _ hattS
    have hic2 : inCheck (play p m) p.turn = true := check_of_adj_kings _ S e p.turn hbS he' hd1
    rw [legal_safe p m hm] at hic2
    exact absurd hic2 (by decide)
  have hSd : S ≠ m.dst := by
    intro hh
    rw [hh, hbdst] at hbS
    have hkk2 : q.kind = .king := congrArg Piece.kind (Option.some.inj hbS).symm
    exact hqk hkk2
  have hSs : S ≠ m.src := by
    intro hh
    rw [hh, play_board_src p m hsd] at hbS
    exact absurd hbS (by simp)
  have hbSp : p.board S = some q := by
    rw [← king_board_change p m hm hk hc S hSs hSd]
    exact hbS
  exact ⟨S, q, hSs, hSd, hbSp, hqc, hqk, hattS⟩

theorem lemmaD_opened (p : Pos) (m : Move) (e S : Sq) (q : Piece) (hc0 : C0 p) (hm : m ∈ legalMoves p)
    (hk : isKingMove p m = true) (hc : isCastle p m = false) (he : kingAt p p.turn.opp e)
    (hS : S ≠ m.src) (hSd : S ≠ m.dst) (hq : p.board S = some q) (hqc : q.color = p.turn)
    (hatt : e ∈ attacks (play p m).board S q) :
    isSlider q.kind = true ∧ inSeg S e m.src = true := by
  have hsd : m.src ≠ m.dst := legal_src_ne_dst p m hm
  have hksrc : p.board m.src = some ⟨p.turn, .king⟩ := kingMove_src p m hm hk
  have hpr : m.promo = none := kingMove_promo p m hm hk
  have hbdst : (play p m).board m.dst = some ⟨p.turn, .king⟩ := by
    rw [play_board_dst, hpr, hksrc]
  have hnoatt : e ∉ attacks p.board S q := by
    intro hmem
    have hattP : attacked p.board e p.turn = true :=
      (attacked_iff _ _ _).mpr ⟨S, q, hq, hqc, hmem⟩
    have hic : inCheck p p.turn.opp = true := by
      rw [inCheck_iff]
      refine ⟨e, he, ?_⟩
      rw [Color.opp_opp]
      exact hattP
    rw [hc0.safe] at hic
    exact absurd hic (by decide)
  obtain ⟨hgeom, hclear⟩ := (mem_attacks_iff _ _ _ _).mp hatt
  have hslider : isSlider q.kind = true := by
    apply Classical.byContradiction
    intro hns
    have hnf : isSlider q.kind = false := (Bool.not_eq_true _).mp hns
    have hmem : e ∈ attacks p.board S q :=
      (mem_attacks_iff _ _ _ _).mpr ⟨hgeom, fun hh => by rw [hh] at hnf; exact absurd hnf (by decide)⟩
    exact hnoatt hmem
  have hcp : clearPath (play p m).board S e := hclear hslider
  have hncp : ¬ clearPath p.board S e := by
    intro hcpp
    exact hnoatt ((mem_attacks_iff _ _ _ _).mpr ⟨hgeom, fun _ => hcpp⟩)
  have hz : ∃ z, inSeg S e z = true ∧ p.board z ≠ none := by
    apply Classical.byContradiction
    intro h
    apply hncp
    intro z hzseg
    apply Classical.byContradiction
    intro hb
    exact h ⟨z, hzseg, hb⟩
  obtain ⟨z, hzseg, hzocc⟩ := hz
  have hzb : (play p m).board z = none := hcp z hzseg
  have hzs2 : z = m.src := by
    apply Classical.byContradiction
    intro hzs
    have hzd : z ≠ m.dst := by
      intro hh
      rw [hh, hbdst] at hzb
      exact absurd hzb (by simp)
    have hbo := king_board_change p m hm hk hc z hzs hzd
    rw [← hbo] at hzocc
    exact hzocc hzb
  rw [hzs2] at hzseg
  exact ⟨hslider, hzseg⟩

theorem aligned_dir (s t : Sq) (h : aligned s t = true) :
    ∃ d ∈ queenD, ∃ k : Nat, 1 ≤ k ∧ fx t = fx s + (k : Int) * d.1 ∧ ry t = ry s + (k : Int) * d.2 := by
  simp only [aligned, Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨hne, hor⟩ := h
  rcases hor with hor | hnat
  · rcases hor with hfx | hry
    · have hryn : ry t - ry s ≠ 0 := fun hh => hne (sq_eq_of_coords s t hfx (by omega))
      refine ⟨(0, isig (ry t - ry s)), rookD_sub_queenD _ (rookD_isig_r _),
        (ry t - ry s).natAbs, Int.natAbs_pos.mpr hryn, ?_, ?_⟩
      · show fx t = fx s + _ * 0
        rw [Int.mul_zero, Int.add_zero]
        omega
      · show ry t = ry s + ((ry t - ry s).natAbs : Int) * isig (ry t - ry s)
        rw [int_mul_isig]
        omega
    · have hfxn : fx t - fx s ≠ 0 := fun hh => hne (sq_eq_of_coords s t (by omega) hry)
      refine ⟨(isig (fx t - fx s), 0), rookD_sub_queenD _ (rookD_isig_l _),
        (fx t - fx s).natAbs, Int.natAbs_pos.mpr hfxn, ?_, ?_⟩
      · show fx t = fx s + ((fx t - fx s).natAbs : Int) * isig (fx t - fx s)
        rw [int_mul_isig]
        omega
      · show ry t = ry s + _ * 0
        rw [Int.mul_zero, Int.add_zero]
        omega
  · have hfxn : fx t - fx s ≠ 0 := fun hh => by
      have e1 : (ry s - ry t).natAbs = 0 := by omega
      have e2 : ry s - ry t = 0 := Int.natAbs_eq_zero.mp e1
      exact hne (sq_eq_of_coords s t (by omega) (by omega))
    refine ⟨(isig (fx t - fx s), isig (ry t - ry s)), bishopD_sub_queenD _ (bishopD_isig _ _),
      (fx t - fx s).natAbs, Int.natAbs_pos.mpr hfxn, ?_, ?_⟩
    · show fx t = fx s + ((fx t - fx s).natAbs : Int) * isig (fx t - fx s)
      rw [int_mul_isig]
      omega
    · show ry t = ry s + ((fx t - fx s).natAbs : Int) * isig (ry t - ry s)
      have e3 : (fx t - fx s).natAbs = (ry t - ry s).natAbs := by omega
      rw [e3, int_mul_isig]
      omega

theorem collinear_para (e src dst : Sq) (df dr : Int) (w : Nat) (hw : 1 ≤ w)
    (h1 : fx src = fx e - (w : Int) * df) (h2 : ry src = ry e - (w : Int) * dr)
    (hcol : collinear e src dst = true) :
    (fx dst - fx e) * dr = (ry dst - ry e) * df := by
  simp only [collinear, beq_iff_eq] at hcol
  have e1 : ry src - ry e = -((w : Int) * dr) := by omega
  have e2 : fx src - fx e = -((w : Int) * df) := by omega
  rw [e1, e2, Int.mul_neg, Int.mul_neg] at hcol
  have key0 : (fx dst - fx e) * ((w : Int) * dr) = (ry dst - ry e) * ((w : Int) * df) := by omega
  have m1 : (fx dst - fx e) * ((w : Int) * dr) = ((fx dst - fx e) * dr) * (w : Int) := by
    rw [Int.mul_comm (w : Int) dr, ← Int.mul_assoc]
  have m2 : (ry dst - ry e) * ((w : Int) * df) = ((ry dst - ry e) * df) * (w : Int) := by
    rw [Int.mul_comm (w : Int) df, ← Int.mul_assoc]
  exact int_mul_cancel _ _ w hw (m1 ▸ m2 ▸ key0)

theorem seg_of_step_on_line_aux (S e dst : Sq) (d : Int × Int) (hd : d ∈ queenD) (k : Nat)
    (hk1k : 1 ≤ k) (hex : fx e = fx S + (k : Int) * d.1) (hey : ry e = ry S + (k : Int) * d.2)
    (i : Nat) (hi1 : 1 ≤ i) (hik : i < k) (u : Int) (hu : u = 1 ∨ u = -1)
    (hdx : fx dst = fx S + ((i : Int) + u) * d.1) (hdy : ry dst = ry S + ((i : Int) + u) * d.2) :
    dst = S ∨ dst = e ∨ inSeg S e dst = true := by
  have hJ0 : 0 ≤ (i : Int) + u := by rcases hu with rfl | rfl <;> omega
  have hJk : (i : Int) + u ≤ (k : Int) := by rcases hu with rfl | rfl <;> omega
  by_cases h0 : (i : Int) + u = 0
  · left
    rw [h0] at hdx hdy
    apply sq_eq_of_coords <;> omega
  · by_cases hkc : (i : Int) + u = (k : Int)
    · right; left
      rw [hkc] at hdx hdy
      apply sq_eq_of_coords <;> omega
    · right; right
      have hJ1 : (1 : Int) ≤ (i : Int) + u := by omega
      have hJlt : (i : Int) + u < (k : Int) := by omega
      have htN : (((i : Int) + u).toNat : Int) = (i : Int) + u := Int.toNat_of_nonneg hJ0
      have h1n : 1 ≤ ((i : Int) + u).toNat := by omega
      have h2n : ((i : Int) + u).toNat < k := by omega
      exact step_seg S e dst d hd k _ hk1k h1n h2n hex hey
        (by rw [htN]; exact hdx) (by rw [htN]; exact hdy)

theorem seg_of_step_on_line (S e src dst : Sq) (hseg : inSeg S e src = true)
    (hon : onLine e src dst = true) (hk1 : kdist src dst = 1) :
    dst = S ∨ dst = e ∨ inSeg S e dst = true := by
  have hseg0 := hseg
  simp only [inSeg, onLine, Bool.and_eq_true, bne_iff_ne] at hseg
  obtain ⟨⟨⟨⟨halign, -⟩, -⟩, -⟩, -⟩ := hseg
  simp only [onLine, Bool.and_eq_true] at hon
  obtain ⟨-, hcol⟩ := hon
  obtain ⟨d, hd, k, hk1k, hex, hey⟩ := aligned_dir S e halign
  obtain ⟨i, hi1, hik, hisx, hisy⟩ := seg_step S e src d hd k hk1k hex hey hseg0
  have eA : fx src = fx e - ((k - i : Nat) : Int) * d.1 := by
    have hcast : ((k - i : Nat) : Int) = (k : Int) - (i : Int) := by omega
    rw [hcast, Int.sub_mul]
    omega
  have eB : ry src = ry e - ((k - i : Nat) : Int) * d.2 := by
    have hcast : ((k - i : Nat) : Int) = (k : Int) - (i : Int) := by omega
    rw [hcast, Int.sub_mul]
    omega
  have hpara := collinear_para e src dst d.1 d.2 (k - i) (by omega) eA eB hcol
  have hmax1 : (fx src - fx dst).natAbs ≤ 1 := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hk1)
  have hmax2 : (ry src - ry dst).natAbs ≤ 1 := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hk1)
  have hdfs : dst ≠ src := fun hh => by
    subst hh
    simp [kdist] at hk1
  rcases queenD_decomp d hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only at hex hey hisx hisy hpara
    have h1 : ry dst = ry S := by omega
    have hff : fx src ≠ fx dst := fun hh => hdfs (sq_eq_of_coords dst src (by omega) (by omega))
    have hu2 : fx dst - fx src = 1 ∨ fx dst - fx src = -1 := by omega
    exact seg_of_step_on_line_aux S e dst _ hd k hk1k hex hey i hi1 hik _ hu2 (by omega) (by omega)
  · dsimp only at hex hey hisx hisy hpara
    have h1 : ry dst = ry S := by omega
    have hff : fx dst ≠ fx src := fun hh => hdfs (sq_eq_of_coords dst src (by omega) (by omega))
    have hu2 : fx src - fx dst = 1 ∨ fx src - fx dst = -1 := by omega
    exact seg_of_step_on_line_aux S e dst _ hd k hk1k hex hey i hi1 hik _ hu2 (by omega) (by omega)
  · dsimp only at hex hey hisx hisy hpara
    have h1 : fx dst = fx S := by omega
    have hff : ry src ≠ ry dst := fun hh => hdfs (sq_eq_of_coords dst src (by omega) (by omega))
    have hu2 : ry dst - ry src = 1 ∨ ry dst - ry src = -1 := by omega
    exact seg_of_step_on_line_aux S e dst _ hd k hk1k hex hey i hi1 hik _ hu2 (by omega) (by omega)
  · dsimp only at hex hey hisx hisy hpara
    have h1 : fx dst = fx S := by omega
    have hff : ry src ≠ ry dst := fun hh => hdfs (sq_eq_of_coords dst src (by omega) (by omega))
    have hu2 : ry src - ry dst = 1 ∨ ry src - ry dst = -1 := by omega
    exact seg_of_step_on_line_aux S e dst _ hd k hk1k hex hey i hi1 hik _ hu2 (by omega) (by omega)
  · dsimp only at hex hey hisx hisy hpara
    have hpd : fx dst - fx src = ry dst - ry src := by omega
    have hff : fx src ≠ fx dst := fun hh => hdfs (sq_eq_of_coords dst src (by omega) (by omega))
    have hu2 : fx dst - fx src = 1 ∨ fx dst - fx src = -1 := by omega
    exact seg_of_step_on_line_aux S e dst _ hd k hk1k hex hey i hi1 hik _ hu2 (by omega) (by omega)
  · dsimp only at hex hey hisx hisy hpara
    have hpd : fx dst - fx src = -(ry dst - ry src) := by omega
    have hff : fx src ≠ fx dst := fun hh => hdfs (sq_eq_of_coords dst src (by omega) (by omega))
    have hu2 : fx dst - fx src = 1 ∨ fx dst - fx src = -1 := by omega
    exact seg_of_step_on_line_aux S e dst _ hd k hk1k hex hey i hi1 hik _ hu2 (by omega) (by omega)
  · dsimp only at hex hey hisx hisy hpara
    have hpd : fx dst - fx src = -(ry dst - ry src) := by omega
    have hff : ry src ≠ ry dst := fun hh => hdfs (sq_eq_of_coords dst src (by omega) (by omega))
    have hu2 : ry dst - ry src = 1 ∨ ry dst - ry src = -1 := by omega
    exact seg_of_step_on_line_aux S e dst _ hd k hk1k hex hey i hi1 hik _ hu2 (by omega) (by omega)
  · dsimp only at hex hey hisx hisy hpara
    have hpd : fx dst - fx src = ry dst - ry src := by omega
    have hffx : fx src ≠ fx dst := fun hh => hdfs (sq_eq_of_coords dst src (by omega) (by omega))
    have hu2 : fx src - fx dst = 1 ∨ fx src - fx dst = -1 := by omega
    exact seg_of_step_on_line_aux S e dst _ hd k hk1k hex hey i hi1 hik _ hu2 (by omega) (by omega)

theorem lemmaD_off_line (p : Pos) (m : Move) (e S : Sq) (q : Piece) (hc0 : C0 p) (hm : m ∈ legalMoves p)
    (hk : isKingMove p m = true) (hc : isCastle p m = false) (he : kingAt p p.turn.opp e)
    (hS : S ≠ m.src) (hSd : S ≠ m.dst) (hq : p.board S = some q) (hqc : q.color = p.turn)
    (hatt : e ∈ attacks (play p m).board S q) (hseg : inSeg S e m.src = true) :
    onLine e m.src m.dst = false := by
  have hksrc : p.board m.src = some ⟨p.turn, .king⟩ := kingMove_src p m hm hk
  have hpr : m.promo = none := kingMove_promo p m hm hk
  have hbdst : (play p m).board m.dst = some ⟨p.turn, .king⟩ := by
    rw [play_board_dst, hpr, hksrc]
  have hk1 := legal_king_step p m hm hk hc
  obtain ⟨hslider, -⟩ := lemmaD_opened p m e S q hc0 hm hk hc he hS hSd hq hqc hatt
  obtain ⟨-, hclear⟩ := (mem_attacks_iff _ _ _ _).mp hatt
  have hcp := hclear hslider
  cases hol : onLine e m.src m.dst with
  | false => rfl
  | true =>
    exfalso
    rcases seg_of_step_on_line S e m.src m.dst hseg hol hk1 with h1 | h2 | h3
    · exact legal_dst_not_own p m hm q (h1 ▸ hq) hqc
    · exact legal_not_capture_king p m hm hc0.safe _ (h2 ▸ he)
    · have hb := hcp m.dst h3
      rw [hbdst] at hb
      exact absurd hb (by simp)

theorem lemmaD (p : Pos) (m : Move) (e : Sq) (hc0 : C0 p) (hm : m ∈ legalMoves p)
    (hk : isKingMove p m = true) (hc : isCastle p m = false) (hg : givesCheck p m = true)
    (he : kingAt p p.turn.opp e) :
    ∃ S q, p.board S = some q ∧ q.color = p.turn ∧ isSlider q.kind = true ∧ inSeg S e m.src = true ∧
      e ∈ attacks (play p m).board S q ∧ aligned m.dst e = false := by
  obtain ⟨S, q, hSs, hSd, hbSp, hqc, hqk, hattS⟩ := lemmaD_checker p m e hc0 hm hk hc hg he
  obtain ⟨hslider, hseg⟩ := lemmaD_opened p m e S q hc0 hm hk hc he hSs hSd hbSp hqc hattS
  have hoffline := lemmaD_off_line p m e S q hc0 hm hk hc he hSs hSd hbSp hqc hattS hseg
  have hk1 := legal_king_step p m hm hk hc
  have hales : aligned e m.src = true := by
    rw [← aligned_comm m.src e]
    exact (inSeg_aligned S e m.src hseg).2.1
  have hksrc : p.board m.src = some ⟨p.turn, .king⟩ := kingMove_src p m hm hk
  have hpr : m.promo = none := kingMove_promo p m hm hk
  have hbdst : (play p m).board m.dst = some ⟨p.turn, .king⟩ := by
    rw [play_board_dst, hpr, hksrc]
  have hnes : e ≠ m.src := by
    intro hh
    rw [hh] at he
    have he2 : p.board m.src = some ⟨p.turn.opp, .king⟩ := he
    rw [hksrc] at he2
    have hcc : p.turn = p.turn.opp := congrArg Piece.color (Option.some.inj he2)
    have hone : ∀ c : Color, c ≠ c.opp := fun c => by cases c <;> decide
    exact absurd hcc (hone p.turn)
  have he' : (play p m).board e = some ⟨p.turn.opp, .king⟩ := king_stay p m hm hc0.safe _ _ he hnes
  have hC0' := c0_play p m hc0 hm
  have hd2 : 2 ≤ kdist m.src e := by
    cases htu : p.turn with
    | white =>
      rw [htu] at hksrc he
      exact hc0.apart m.src e hksrc he
    | black =>
      rw [htu] at hksrc he
      have h := hc0.apart e m.src he hksrc
      rw [kdist_comm] at h
      exact h
  have hd2' : 2 ≤ kdist m.dst e := by
    cases htu : p.turn with
    | white =>
      rw [htu] at hbdst he'
      exact hC0'.apart m.dst e hbdst he'
    | black =>
      rw [htu] at hbdst he'
      have h := hC0'.apart e m.dst he' hbdst
      rw [kdist_comm] at h
      exact h
  have hald := lemmaG e m.src m.dst hales hd2 hk1 hoffline hd2'
  exact ⟨S, q, hbSp, hqc, hslider, hseg, hattS, hald⟩

theorem lemmaD_aligned (p : Pos) (m : Move) (e : Sq) (hc0 : C0 p) (hm : m ∈ legalMoves p)
    (hk : isKingMove p m = true) (hc : isCastle p m = false) (hg : givesCheck p m = true)
    (he : kingAt p p.turn.opp e) : aligned m.src e = true := by
  obtain ⟨S, q, hSs, hSd, hbSp, hqc, hqk, hattS⟩ := lemmaD_checker p m e hc0 hm hk hc hg he
  obtain ⟨-, hseg⟩ := lemmaD_opened p m e S q hc0 hm hk hc he hSs hSd hbSp hqc hattS
  exact (inSeg_aligned S e m.src hseg).2.1

theorem lemmaD_seg_empty (p : Pos) (m : Move) (e : Sq) (hc0 : C0 p) (hm : m ∈ legalMoves p)
    (hk : isKingMove p m = true) (hc : isCastle p m = false) (hg : givesCheck p m = true)
    (he : kingAt p p.turn.opp e) : ∀ z, inSeg m.src e z = true → p.board z = none := by
  obtain ⟨S, q, hSs, hSd, hbSp, hqc, hqk, hattS⟩ := lemmaD_checker p m e hc0 hm hk hc hg he
  obtain ⟨hslider, hseg⟩ := lemmaD_opened p m e S q hc0 hm hk hc he hSs hSd hbSp hqc hattS
  obtain ⟨-, hclear⟩ := (mem_attacks_iff _ _ _ _).mp hattS
  have hcp := hclear hslider
  have hksrc : p.board m.src = some ⟨p.turn, .king⟩ := kingMove_src p m hm hk
  have hpr : m.promo = none := kingMove_promo p m hm hk
  have hbdst : (play p m).board m.dst = some ⟨p.turn, .king⟩ := by
    rw [play_board_dst, hpr, hksrc]
  intro z hz
  have hA : inSeg e S m.src = true := inSeg_comm S e m.src ▸ hseg
  have hB : inSeg e m.src z = true := inSeg_comm m.src e z ▸ hz
  have hz' : inSeg S e z = true := inSeg_comm e S z ▸ inSeg_trans e S m.src z hA hB
  have hzs : z ≠ m.src := by
    have h := hz
    simp only [inSeg, onLine, Bool.and_eq_true, bne_iff_ne] at h
    exact h.1.1.2
  have hzd : z ≠ m.dst := by
    intro hh
    have hb := hcp z hz'
    rw [hh, hbdst] at hb
    exact absurd hb (by simp)
  have hbo := king_board_change p m hm hk hc z hzs hzd
  have hzb : (play p m).board z = none := hcp z hz'
  rw [hbo] at hzb
  exact hzb

end Chess.C364
