import ChessProof.C364.LemmaD

namespace Chess.C364

open Chess

def posAt (p : Pos) (ms : List Move) (j : Nat) : Pos := after p (ms.take j)

def kingTo (c : Color) (ks : Bool) : Sq := sq (if ks then 6 else 2) c.home

def rookTo (c : Color) (ks : Bool) : Sq := sq (if ks then 5 else 3) c.home

def castleSide (m : Move) : Bool := m.dst.file == 6

theorem checkSeq_step (p : Pos) (ms : List Move) (hs : IsCheckSeq p ms) (j : Nat) (hj : j < ms.length) :
    ms[j] ∈ legalMoves (posAt p ms j) ∧ givesCheck (posAt p ms j) ms[j] = true ∧
      posAt p ms (j + 1) = play (posAt p ms j) ms[j] := by
  induction ms generalizing p j with
  | nil => exact absurd hj (by simp)
  | cons m ms ih =>
    obtain ⟨hm, hg, hs'⟩ : m ∈ legalMoves p ∧ givesCheck p m = true ∧ IsCheckSeq (play p m) ms := hs
    cases j with
    | zero => exact ⟨hm, hg, rfl⟩
    | succ j =>
      have hj' : j < ms.length := by
        have : j + 1 < ms.length + 1 := hj
        omega
      exact ih (play p m) hs' j hj'

theorem checkSeq_reachable (p : Pos) (ms : List Move) (hr : Reachable p) (hs : IsCheckSeq p ms) (j : Nat)
    (hj : j ≤ ms.length) : Reachable (posAt p ms j) := by
  induction j with
  | zero => exact hr
  | succ j ih =>
    have hjj : j < ms.length := Nat.lt_of_succ_le hj
    obtain ⟨hml, -, hpl⟩ := checkSeq_step p ms hs j hjj
    rw [hpl]
    exact Reachable.step (ih (Nat.le_of_succ_le hj)) hml

theorem checkSeq_inCheck (p : Pos) (ms : List Move) (hs : IsCheckSeq p ms) (j : Nat) (h1 : 1 ≤ j)
    (hj : j ≤ ms.length) : inCheck (posAt p ms j) (posAt p ms j).turn = true := by
  cases j with
  | zero => omega
  | succ j =>
    have hjj : j < ms.length := Nat.lt_of_succ_le hj
    obtain ⟨hml, hg, hpl⟩ := checkSeq_step p ms hs j hjj
    rw [hpl]
    exact hg

theorem K1_castle_first (p : Pos) (ms : List Move) (hr : Reachable p) (hs : IsCheckSeq p ms) (j : Nat) (h1 : 1 ≤ j)
    (hj : j < ms.length) : isCastle (posAt p ms j) ms[j] = false := by
  obtain ⟨hml, -, -⟩ := checkSeq_step p ms hs j hj
  have hic := checkSeq_inCheck p ms hs j h1 (Nat.le_of_lt hj)
  have hrc := reachable_c0 _ (checkSeq_reachable p ms hr hs j (Nat.le_of_lt hj))
  cases hc : isCastle (posAt p ms j) ms[j] with
  | false => rfl
  | true =>
    exfalso
    have hmem := legal_castle_mem _ _ hml hc
    have h2 := castleMoves_not_in_check _ hrc _ hmem
    rw [h2] at hic
    exact absurd hic (by decide)

theorem kings_fixed (p : Pos) (ms : List Move) (hr : Reachable p) (hs : IsCheckSeq p ms) (i j : Nat)
    (hij : i ≤ j) (hj : j ≤ ms.length)
    (hnk : ∀ k (hk : k < ms.length), i ≤ k → k < j → isKingMove (posAt p ms k) ms[k] = false)
    (c : Color) (s : Sq) : kingAt (posAt p ms j) c s ↔ kingAt (posAt p ms i) c s := by
  have key : ∀ d, i + d ≤ j →
      (kingAt (posAt p ms (i + d)) c s ↔ kingAt (posAt p ms i) c s) := by
    intro d hdj
    induction d with
    | zero => exact Iff.rfl
    | succ d ih =>
      have hlt : i + d < ms.length := by omega
      obtain ⟨hml, -, hpl⟩ := checkSeq_step p ms hs (i + d) hlt
      show kingAt (posAt p ms (i + d + 1)) c s ↔ kingAt (posAt p ms i) c s
      rw [hpl]
      have hsafe := (reachable_c0 _
        (checkSeq_reachable p ms hr hs (i + d) (Nat.le_of_lt hlt))).safe
      exact (kingAt_play_nonking _ _ hml (hnk _ hlt (Nat.le_add_right i d) (by omega)) hsafe c s).trans
        (ih (by omega))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hij
  rw [hd]
  exact key d (Nat.le_of_eq hd.symm)

theorem king_ply_dst (p : Pos) (m : Move) (hc0 : C0 p) (hm : m ∈ legalMoves p) (hk : isKingMove p m = true) :
    kingAt (play p m) p.turn m.dst := by
  have hksrc := kingMove_src p m hm hk
  have hpr := kingMove_promo p m hm hk
  show (play p m).board m.dst = some ⟨p.turn, .king⟩
  rw [play_board_dst, hpr, hksrc]

theorem king_square_unique (p : Pos) (hc0 : C0 p) (c : Color) (s t : Sq) (hs : kingAt p c s)
    (ht : kingAt p c t) : s = t := by
  cases c with
  | white =>
    obtain ⟨w, hw⟩ := hc0.wk
    exact ((hw s).mp hs).trans ((hw t).mp ht).symm
  | black =>
    obtain ⟨b, hb⟩ := hc0.bk
    exact ((hb s).mp hs).trans ((hb t).mp ht).symm

theorem king_square_exists (p : Pos) (hc0 : C0 p) (c : Color) : ∃ s, kingAt p c s := by
  cases c with
  | white =>
    obtain ⟨w, hw⟩ := hc0.wk
    exact ⟨w, (hw w).mpr rfl⟩
  | black =>
    obtain ⟨b, hb⟩ := hc0.bk
    exact ⟨b, (hb b).mpr rfl⟩

theorem K2_two_plain (p : Pos) (ms : List Move) (hr : Reachable p) (hs : IsCheckSeq p ms) (i j : Nat)
    (hij : i < j) (hj : j < ms.length)
    (hki : isKingMove (posAt p ms i) ms[i] = true) (hci : isCastle (posAt p ms i) ms[i] = false)
    (hkj : isKingMove (posAt p ms j) ms[j] = true)
    (hnk : ∀ k (hk : k < ms.length), i < k → k < j → isKingMove (posAt p ms k) ms[k] = false) : False := by
  have hilt : i < ms.length := Nat.lt_trans hij hj
  obtain ⟨hmi, hgi, hpli⟩ := checkSeq_step p ms hs i hilt
  obtain ⟨hmj, hgj, -⟩ := checkSeq_step p ms hs j hj
  have hc0i : C0 (posAt p ms i) := reachable_c0 _
    (checkSeq_reachable p ms hr hs i (Nat.le_of_lt hilt))
  have hc0j : C0 (posAt p ms j) := reachable_c0 _ (checkSeq_reachable p ms hr hs j (Nat.le_of_lt hj))
  obtain ⟨e, he⟩ := king_square_exists _ hc0i (posAt p ms i).turn.opp
  obtain ⟨-, -, -, -, -, -, -, haligni⟩ := lemmaD _ ms[i] e hc0i hmi hki hci hgi he
  obtain ⟨e', he'⟩ := king_square_exists _ hc0j (posAt p ms j).turn.opp
  have hcj : isCastle (posAt p ms j) ms[j] = false := K1_castle_first p ms hr hs j (by omega) hj
  have halignj := lemmaD_aligned _ ms[j] e' hc0j hmj hkj hcj hgj he'
  have hsrci : (posAt p ms i).board ms[i].src = some ⟨(posAt p ms i).turn, .king⟩ :=
    kingMove_src _ _ hmi hki
  have hdstk : kingAt (play (posAt p ms i) ms[i]) (posAt p ms i).turn ms[i].dst :=
    king_ply_dst _ _ hc0i hmi hki
  have hene : e ≠ ms[i].src := by
    intro hh
    rw [hh] at he
    rw [he] at hsrci
    simp only [Option.some.injEq, Piece.mk.injEq] at hsrci
    cases ht : (posAt p ms i).turn with
    | white => rw [ht] at hsrci; exact absurd hsrci.1 (by decide)
    | black => rw [ht] at hsrci; exact absurd hsrci.1 (by decide)
  have hestay : kingAt (play (posAt p ms i) ms[i]) (posAt p ms i).turn.opp e :=
    king_stay _ _ hmi hc0i.safe _ e he hene
  have hkf : ∀ (c : Color) (s : Sq), kingAt (posAt p ms j) c s ↔
      kingAt (posAt p ms (i + 1)) c s :=
    fun c s => kings_fixed p ms hr hs (i + 1) j hij (Nat.le_of_lt hj)
      (fun k hk hi1 hkj2 => hnk k hk hi1 hkj2) c s
  have hdstj : kingAt (posAt p ms j) (posAt p ms i).turn ms[i].dst := by
    have h1 := (hkf (posAt p ms i).turn ms[i].dst).mpr ?_
    · exact h1
    · rw [hpli]; exact hdstk
  have hej : kingAt (posAt p ms j) (posAt p ms i).turn.opp e := by
    have h1 := (hkf (posAt p ms i).turn.opp e).mpr ?_
    · exact h1
    · rw [hpli]; exact hestay
  have hsrcj : kingAt (posAt p ms j) (posAt p ms j).turn ms[j].src :=
    kingMove_src _ _ hmj hkj
  by_cases hturn : (posAt p ms j).turn = (posAt p ms i).turn
  · rw [← hturn] at hdstj hej
    have hsrceq : ms[j].src = ms[i].dst := king_square_unique _ hc0j _ _ _ hsrcj hdstj
    have heeq : e' = e :=
      king_square_unique _ hc0j _ _ _ he' hej
    rw [hsrceq, heeq] at halignj
    rw [halignj] at haligni
    exact absurd haligni (by decide)
  · have htopp : (posAt p ms j).turn = (posAt p ms i).turn.opp :=
      color_eq_opp_of_ne _ _ hturn
    have hoo : (posAt p ms j).turn.opp = (posAt p ms i).turn := by
      rw [htopp, Color.opp_opp]
    rw [← htopp] at hej
    rw [← hoo] at hdstj
    have hsrceq : ms[j].src = e := king_square_unique _ hc0j _ _ _ hsrcj hej
    have heeq : e' = ms[i].dst := king_square_unique _ hc0j _ _ _ he' hdstj
    rw [hsrceq, heeq] at halignj
    rw [aligned_comm] at halignj
    rw [halignj] at haligni
    exact absurd haligni (by decide)

theorem castle_shape (p : Pos) (m : Move) (hm : m ∈ legalMoves p) (hc : isCastle p m = true) :
    m.src = sq 4 p.turn.home ∧ m.dst = kingTo p.turn (castleSide m) ∧
      p.board (sq (if castleSide m then 7 else 0) p.turn.home) = some ⟨p.turn, .rook⟩ ∧
      (play p m).board (rookTo p.turn (castleSide m)) = some ⟨p.turn, .rook⟩ ∧
      attacked p.board (rookTo p.turn (castleSide m)) p.turn.opp = false := by
  have hmem := legal_castle_mem p m hm hc
  unfold castleMoves at hmem
  dsimp only at hmem
  by_cases hout : ((p.board (sq 4 p.turn.home) == some ⟨p.turn, .king⟩) &&
      !attacked p.board (sq 4 p.turn.home) p.turn.opp) = true
  · obtain ⟨hk4b, hs4b⟩ := Bool.and_eq_true _ _ |>.mp hout
    have hk4 : p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ := beq_iff_eq.mp hk4b
    rw [if_pos hout, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · by_cases hK : ((p.castleK p.turn && p.board (sq 7 p.turn.home) == some ⟨p.turn, .rook⟩ &&
          [5, 6].all fun f => empty p.board (sq f p.turn.home)) &&
          !attacked p.board (sq 5 p.turn.home) p.turn.opp) = true
      · rw [if_pos hK, List.mem_singleton] at hmem
        obtain rfl := hmem
        obtain ⟨hK1, hs5b⟩ := Bool.and_eq_true _ _ |>.mp hK
        obtain ⟨hK2, -⟩ := Bool.and_eq_true _ _ |>.mp hK1
        obtain ⟨-, hr7b⟩ := Bool.and_eq_true _ _ |>.mp hK2
        have hr7 : p.board (sq 7 p.turn.home) = some ⟨p.turn, .rook⟩ := beq_iff_eq.mp hr7b
        have hs5 : attacked p.board (sq 5 p.turn.home) p.turn.opp = false := by
          cases hh : attacked p.board (sq 5 p.turn.home) p.turn.opp with
          | false => rfl
          | true => rw [hh] at hs5b; exact absurd hs5b (by decide)
        have hcs : castleSide ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ = true := by
          unfold castleSide
          rw [file_sq 6 _ (by decide) (home_lt _)]
          rfl
        refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · rw [hcs]
          rfl
        · rw [hcs]
          exact hr7
        · rw [hcs]
          show (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board (sq 5 p.turn.home) =
            some ⟨p.turn, .rook⟩
          rw [play_board_castleK p hk4 (sq 5 p.turn.home),
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 5 6 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 5 4 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_self_eq_true]
          exact hr7
        · rw [hcs]
          exact hs5
      · rw [if_neg hK] at hmem
        exact absurd hmem (not_mem_nil' m)
    · by_cases hQ : ((p.castleQ p.turn && p.board (sq 0 p.turn.home) == some ⟨p.turn, .rook⟩ &&
          [1, 2, 3].all fun f => empty p.board (sq f p.turn.home)) &&
          !attacked p.board (sq 3 p.turn.home) p.turn.opp) = true
      · rw [if_pos hQ, List.mem_singleton] at hmem
        obtain rfl := hmem
        obtain ⟨hQ1, hs3b⟩ := Bool.and_eq_true _ _ |>.mp hQ
        obtain ⟨hQ2, -⟩ := Bool.and_eq_true _ _ |>.mp hQ1
        obtain ⟨-, hr0b⟩ := Bool.and_eq_true _ _ |>.mp hQ2
        have hr0 : p.board (sq 0 p.turn.home) = some ⟨p.turn, .rook⟩ := beq_iff_eq.mp hr0b
        have hs3 : attacked p.board (sq 3 p.turn.home) p.turn.opp = false := by
          cases hh : attacked p.board (sq 3 p.turn.home) p.turn.opp with
          | false => rfl
          | true => rw [hh] at hs3b; exact absurd hs3b (by decide)
        have hcs : castleSide ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ = false := by
          unfold castleSide
          rw [file_sq 2 _ (by decide) (home_lt _)]
          rfl
        refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · rw [hcs]
          rfl
        · rw [hcs]
          exact hr0
        · rw [hcs]
          show (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board (sq 3 p.turn.home) =
            some ⟨p.turn, .rook⟩
          rw [play_board_castleQ p hk4 (sq 3 p.turn.home),
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 3 2 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 3 4 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_self_eq_true]
          exact hr0
        · rw [hcs]
          exact hs3
      · rw [if_neg hQ] at hmem
        exact absurd hmem (not_mem_nil' m)
  · rw [if_neg hout] at hmem
    exact absurd hmem (not_mem_nil' m)

def castleCheckerCheck : Bool :=
  [Color.white, Color.black].all fun c => [true, false].all fun ks => allSq.all fun S => allSq.all fun e =>
    !((inSeg S e (sq 4 c.home) || inSeg S e (sq (if ks then 7 else 0) c.home)) &&
      !(inSeg S e (kingTo c ks)) && !(inSeg S e (rookTo c ks)) &&
      (e != kingTo c ks) && (e != rookTo c ks) && (e != sq 4 c.home) &&
      (e != sq (if ks then 7 else 0) c.home) &&
      (S != kingTo c ks) && (S != sq 4 c.home) && (S != sq (if ks then 7 else 0) c.home) &&
      (S != rookTo c ks) && (S != e))

set_option maxRecDepth 100000 in
theorem castleCheckerCheck_true : castleCheckerCheck = true := by decide +kernel

theorem castle_checker_geom (c : Color) (ks : Bool) (S e : Sq)
    (hseg : (inSeg S e (sq 4 c.home) || inSeg S e (sq (if ks then 7 else 0) c.home)) = true)
    (hK : inSeg S e (kingTo c ks) = false) (hR : inSeg S e (rookTo c ks) = false)
    (heK : e ≠ kingTo c ks) (heR : e ≠ rookTo c ks) (he4 : e ≠ sq 4 c.home)
    (hec : e ≠ sq (if ks then 7 else 0) c.home)
    (hSK : S ≠ kingTo c ks) (hS4 : S ≠ sq 4 c.home)
    (hSc : S ≠ sq (if ks then 7 else 0) c.home) (hSe : S ≠ e) :
    S = rookTo c ks := by
  by_cases hSR : S = rookTo c ks
  · exact hSR
  exfalso
  have h := castleCheckerCheck_true
  simp only [castleCheckerCheck, List.all_eq_true] at h
  have h2 := h c (by cases c <;> simp) ks (by cases ks <;> simp) S (mem_allSq S) e (mem_allSq e)
  have b2 : (!inSeg S e (kingTo c ks)) = true := by rw [hK]; decide
  have b3 : (!inSeg S e (rookTo c ks)) = true := by rw [hR]; decide
  have b4 := bne_iff_ne.mpr heK
  have b5 := bne_iff_ne.mpr heR
  have b6 := bne_iff_ne.mpr he4
  have b7 := bne_iff_ne.mpr hec
  have b8 := bne_iff_ne.mpr hSK
  have b9 := bne_iff_ne.mpr hS4
  have b10 := bne_iff_ne.mpr hSc
  have b11 := bne_iff_ne.mpr hSR
  have b12 := bne_iff_ne.mpr hSe
  have hall : ((inSeg S e (sq 4 c.home) || inSeg S e (sq (if ks then 7 else 0) c.home)) &&
      !(inSeg S e (kingTo c ks)) && !(inSeg S e (rookTo c ks)) &&
      (e != kingTo c ks) && (e != rookTo c ks) && (e != sq 4 c.home) &&
      (e != sq (if ks then 7 else 0) c.home) &&
      (S != kingTo c ks) && (S != sq 4 c.home) && (S != sq (if ks then 7 else 0) c.home) &&
      (S != rookTo c ks) && (S != e)) = true := by
    rw [hseg, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]
    rfl
  rw [hall] at h2
  exact absurd h2 (by decide)

def cornerSegCheck : Bool :=
  allSq.all fun a => allSq.all fun b => allSq.all fun z =>
    !(inSeg a b z) || !((fx z == 0 || fx z == 7) && (ry z == 0 || ry z == 7))

set_option maxRecDepth 100000 in
theorem cornerSegCheck_true : cornerSegCheck = true := by decide +kernel

theorem corner_inSeg_false (a b z : Sq) (hf : (fx z == 0 || fx z == 7) = true)
    (hr : (ry z == 0 || ry z == 7) = true) (h : inSeg a b z = true) : False := by
  have hchk := cornerSegCheck_true
  simp only [cornerSegCheck, List.all_eq_true] at hchk
  have h2 := hchk a (mem_allSq a) b (mem_allSq b) z (mem_allSq z)
  rw [h, Bool.not_true, hf, hr, Bool.and_self, Bool.not_true, Bool.or_self] at h2
  exact absurd h2 (by decide)

theorem corner_if_home_fx (c : Color) (ks : Bool) :
    (fx (sq (if ks then 7 else 0) c.home) == 0 || fx (sq (if ks then 7 else 0) c.home) == 7) = true := by
  rw [fx_sq _ _ (by cases ks <;> decide) (home_lt _)]
  cases ks <;> rfl

theorem corner_if_home_ry (c : Color) (ks : Bool) :
    (ry (sq (if ks then 7 else 0) c.home) == 0 || ry (sq (if ks then 7 else 0) c.home) == 7) = true := by
  rw [ry_sq _ _ (by cases ks <;> decide) (home_lt _)]
  cases c <;> rfl

def castleSegCheck : Bool :=
  [Color.white, Color.black].all fun c => [true, false].all fun ks => allSq.all fun e => allSq.all fun z =>
    !((ry e == (c.home : Int)) && inSeg (kingTo c ks) e (rookTo c ks) && inSeg (rookTo c ks) e z) ||
      ((ry z == (c.home : Int)) && inSeg z (kingTo c ks) (rookTo c ks) &&
        !knightJump z (kingTo c ks) && !diagLine z (kingTo c ks))

set_option maxRecDepth 100000 in
theorem castleSegCheck_true : castleSegCheck = true := by decide +kernel

theorem castle_seg_facts (c : Color) (ks : Bool) (e z : Sq)
    (he : ry e = (c.home : Int)) (hR : inSeg (kingTo c ks) e (rookTo c ks) = true)
    (hz : inSeg (rookTo c ks) e z = true) :
    ry z = (c.home : Int) ∧ inSeg z (kingTo c ks) (rookTo c ks) = true ∧
      knightJump z (kingTo c ks) = false ∧ diagLine z (kingTo c ks) = false := by
  have h := castleSegCheck_true
  simp only [castleSegCheck, List.all_eq_true] at h
  have h2 := h c (by cases c <;> simp) ks (by cases ks <;> simp) e (mem_allSq e) z (mem_allSq z)
  have b1 : (ry e == (c.home : Int)) = true := beq_iff_eq.mpr he
  have hpre : ((ry e == (c.home : Int)) && inSeg (kingTo c ks) e (rookTo c ks) &&
      inSeg (rookTo c ks) e z) = true := by
    rw [b1, hR, hz]
    rfl
  rw [hpre, Bool.not_true, Bool.false_or] at h2
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
  obtain ⟨⟨⟨hzr, hzKR⟩, hkn⟩, hdg⟩ := h2
  refine ⟨beq_iff_eq.mp hzr, hzKR, ?_, ?_⟩
  · cases hh : knightJump z (kingTo c ks) with
    | false => rfl
    | true => rw [hh] at hkn; exact absurd hkn (by decide)
  · cases hh : diagLine z (kingTo c ks) with
    | false => rfl
    | true => rw [hh] at hdg; exact absurd hdg (by decide)

theorem geomAttack_seg (c : Color) (k : Kind) (s t z : Sq) (hsl : isSlider k = true)
    (hseg : inSeg s t z = true) (hg : geomAttack c k s t = true) : geomAttack c k s z = true := by
  have hzs : z ≠ s := (inSeg_ne hseg).1
  have hst : s ≠ t := by
    have hal0 := aligned_ab_of_inSeg hseg
    simp only [aligned, Bool.and_eq_true, bne_iff_ne] at hal0
    exact hal0.1
  have halZ : aligned s z = true := (inSeg_aligned s t z hseg).1
  have hcol : (fx z - fx s) * (ry t - ry s) = (ry z - ry s) * (fx t - fx s) := by
    have h2 := hseg
    simp only [inSeg, onLine, Bool.and_eq_true] at h2
    have h3 := h2.1.1.1.2
    simp only [collinear, beq_iff_eq] at h3
    exact h3
  cases k with
  | pawn => exact absurd hsl (by decide)
  | knight => exact absurd hsl (by decide)
  | bishop =>
    simp only [geomAttack, diagLine, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at hg ⊢
    obtain ⟨-, hfxT, hryT⟩ := hg
    refine ⟨halZ, fun hfx => ?_, fun hry => ?_⟩
    · have h2 : fx z - fx s = 0 := by omega
      rw [h2, Int.zero_mul] at hcol
      rcases Int.mul_eq_zero.mp hcol.symm with h3 | h3
      · exact hzs (sq_eq_of_coords z s hfx.symm (by omega))
      · exact hfxT (by omega)
    · have h2 : ry z - ry s = 0 := by omega
      rw [h2, Int.zero_mul] at hcol
      rcases Int.mul_eq_zero.mp hcol with h3 | h3
      · exact hzs (sq_eq_of_coords z s (by omega) hry.symm)
      · exact hryT (by omega)
  | rook =>
    simp only [geomAttack, orthLine, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hg ⊢
    obtain ⟨-, hor⟩ := hg
    refine ⟨halZ, ?_⟩
    rcases hor with hfx | hry
    · have h2 : fx t - fx s = 0 := by omega
      rw [h2, Int.mul_zero] at hcol
      rcases Int.mul_eq_zero.mp hcol with h3 | h3
      · exact Or.inl (by omega)
      · exact absurd (sq_eq_of_coords s t hfx (by omega)) hst
    · have h2 : ry t - ry s = 0 := by omega
      rw [h2, Int.mul_zero] at hcol
      rcases Int.mul_eq_zero.mp hcol.symm with h3 | h3
      · exact Or.inr (by omega)
      · exact absurd (sq_eq_of_coords s t (by omega) hry) hst
  | queen =>
    simp only [geomAttack]
    exact halZ
  | king => exact absurd hsl (by decide)

theorem castle_play_facts (p : Pos) (m : Move) (hm : m ∈ legalMoves p) (hc : isCastle p m = true) :
    (∀ z, z ≠ sq 4 p.turn.home → z ≠ sq (if castleSide m then 7 else 0) p.turn.home →
      z ≠ kingTo p.turn (castleSide m) → z ≠ rookTo p.turn (castleSide m) →
      (play p m).board z = p.board z) ∧
    (play p m).board (kingTo p.turn (castleSide m)) = some ⟨p.turn, .king⟩ ∧
    (play p m).board (rookTo p.turn (castleSide m)) = some ⟨p.turn, .rook⟩ ∧
    (play p m).board (sq 4 p.turn.home) = none ∧
    (play p m).board (sq (if castleSide m then 7 else 0) p.turn.home) = none ∧
    attacked p.board (rookTo p.turn (castleSide m)) p.turn.opp = false ∧
    attacked p.board (sq 4 p.turn.home) p.turn.opp = false := by
  obtain hmem := legal_castle_mem p m hm hc
  unfold castleMoves at hmem
  dsimp only at hmem
  by_cases hout : ((p.board (sq 4 p.turn.home) == some ⟨p.turn, .king⟩) &&
      !attacked p.board (sq 4 p.turn.home) p.turn.opp) = true
  · obtain ⟨hk4b, hs4b⟩ := Bool.and_eq_true _ _ |>.mp hout
    have hk4 : p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ := beq_iff_eq.mp hk4b
    have hs4 : attacked p.board (sq 4 p.turn.home) p.turn.opp = false := by
      cases hh : attacked p.board (sq 4 p.turn.home) p.turn.opp with
      | false => rfl
      | true => rw [hh] at hs4b; exact absurd hs4b (by decide)
    rw [if_pos hout, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · by_cases hK : ((p.castleK p.turn && p.board (sq 7 p.turn.home) == some ⟨p.turn, .rook⟩ &&
          [5, 6].all fun f => empty p.board (sq f p.turn.home)) &&
          !attacked p.board (sq 5 p.turn.home) p.turn.opp) = true
      · rw [if_pos hK, List.mem_singleton] at hmem
        obtain rfl := hmem
        obtain ⟨hK1, hs5b⟩ := Bool.and_eq_true _ _ |>.mp hK
        obtain ⟨hK2, -⟩ := Bool.and_eq_true _ _ |>.mp hK1
        obtain ⟨-, hr7b⟩ := Bool.and_eq_true _ _ |>.mp hK2
        have hr7 : p.board (sq 7 p.turn.home) = some ⟨p.turn, .rook⟩ := beq_iff_eq.mp hr7b
        have hs5 : attacked p.board (sq 5 p.turn.home) p.turn.opp = false := by
          cases hh : attacked p.board (sq 5 p.turn.home) p.turn.opp with
          | false => rfl
          | true => rw [hh] at hs5b; exact absurd hs5b (by decide)
        have hcs : castleSide ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ = true := by
          unfold castleSide
          rw [file_sq 6 _ (by decide) (home_lt _)]
          rfl
        rw [hcs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show ∀ z, z ≠ sq 4 p.turn.home → z ≠ sq 7 p.turn.home → z ≠ sq 6 p.turn.home →
              z ≠ sq 5 p.turn.home →
              (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board z = p.board z
          intro z h4 h7 h6 h5
          rw [play_board_castleK p hk4 z, beq_eq_false_iff_ne.mpr h6, beq_eq_false_iff_ne.mpr h4,
            beq_eq_false_iff_ne.mpr h5, beq_eq_false_iff_ne.mpr h7]
          rfl
        · show (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board (sq 6 p.turn.home) =
            some ⟨p.turn, .king⟩
          rw [play_board_castleK p hk4, beq_self_eq_true]
          exact hk4
        · show (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board (sq 5 p.turn.home) =
            some ⟨p.turn, .rook⟩
          rw [play_board_castleK p hk4,
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 5 6 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 5 4 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_self_eq_true]
          exact hr7
        · show (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board (sq 4 p.turn.home) = none
          rw [play_board_castleK p hk4,
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 4 6 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_self_eq_true]
          rfl
        · show (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board (sq 7 p.turn.home) = none
          rw [play_board_castleK p hk4,
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 7 6 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 7 4 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 7 5 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_self_eq_true]
          rfl
        · exact hs5
        · exact hs4
      · rw [if_neg hK] at hmem
        exact absurd hmem (not_mem_nil' m)
    · by_cases hQ : ((p.castleQ p.turn && p.board (sq 0 p.turn.home) == some ⟨p.turn, .rook⟩ &&
          [1, 2, 3].all fun f => empty p.board (sq f p.turn.home)) &&
          !attacked p.board (sq 3 p.turn.home) p.turn.opp) = true
      · rw [if_pos hQ, List.mem_singleton] at hmem
        obtain rfl := hmem
        obtain ⟨hQ1, hs3b⟩ := Bool.and_eq_true _ _ |>.mp hQ
        obtain ⟨hQ2, -⟩ := Bool.and_eq_true _ _ |>.mp hQ1
        obtain ⟨-, hr0b⟩ := Bool.and_eq_true _ _ |>.mp hQ2
        have hr0 : p.board (sq 0 p.turn.home) = some ⟨p.turn, .rook⟩ := beq_iff_eq.mp hr0b
        have hs3 : attacked p.board (sq 3 p.turn.home) p.turn.opp = false := by
          cases hh : attacked p.board (sq 3 p.turn.home) p.turn.opp with
          | false => rfl
          | true => rw [hh] at hs3b; exact absurd hs3b (by decide)
        have hcs : castleSide ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ = false := by
          unfold castleSide
          rw [file_sq 2 _ (by decide) (home_lt _)]
          rfl
        rw [hcs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show ∀ z, z ≠ sq 4 p.turn.home → z ≠ sq 0 p.turn.home → z ≠ sq 2 p.turn.home →
              z ≠ sq 3 p.turn.home →
              (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board z = p.board z
          intro z h4 h0 h2 h3
          rw [play_board_castleQ p hk4 z, beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h4,
            beq_eq_false_iff_ne.mpr h3, beq_eq_false_iff_ne.mpr h0]
          rfl
        · show (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board (sq 2 p.turn.home) =
            some ⟨p.turn, .king⟩
          rw [play_board_castleQ p hk4, beq_self_eq_true]
          exact hk4
        · show (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board (sq 3 p.turn.home) =
            some ⟨p.turn, .rook⟩
          rw [play_board_castleQ p hk4,
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 3 2 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 3 4 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_self_eq_true]
          exact hr0
        · show (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board (sq 4 p.turn.home) = none
          rw [play_board_castleQ p hk4,
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 4 2 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_self_eq_true]
          rfl
        · show (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board (sq 0 p.turn.home) = none
          rw [play_board_castleQ p hk4,
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 0 2 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 0 4 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_eq_false_iff_ne.mpr (sq_ne_of_file 0 3 (by decide) (by decide) _ (home_lt _)
              (by decide)),
            beq_self_eq_true]
          rfl
        · exact hs3
        · exact hs4
      · rw [if_neg hQ] at hmem
        exact absurd hmem (not_mem_nil' m)
  · rw [if_neg hout] at hmem
    exact absurd hmem (not_mem_nil' m)

theorem castle_checker_aux (p : Pos) (b' : Board) (turn : Color) (ks : Bool) (e S : Sq) (q : Piece)
    (hapart : ∀ w b2, b' w = some ⟨.white, .king⟩ → b' b2 = some ⟨.black, .king⟩ → 2 ≤ kdist w b2)
    (hsafe' : ∀ S' q', p.board S' = some q' → q'.color = turn → e ∉ attacks p.board S' q')
    (hchg : ∀ z, z ≠ sq 4 turn.home → z ≠ sq (if ks then 7 else 0) turn.home →
      z ≠ kingTo turn ks → z ≠ rookTo turn ks → b' z = p.board z)
    (hbK : b' (kingTo turn ks) = some ⟨turn, .king⟩)
    (hbR : b' (rookTo turn ks) = some ⟨turn, .rook⟩)
    (hb4 : b' (sq 4 turn.home) = none)
    (hbc : b' (sq (if ks then 7 else 0) turn.home) = none)
    (he : b' e = some ⟨turn.opp, .king⟩)
    (hbS : b' S = some q) (hqc : q.color = turn) (hattS : e ∈ attacks b' S q) :
    S = rookTo turn ks := by
  by_cases hSR : S = rookTo turn ks
  · exact hSR
  exfalso
  have hSe : S ≠ e := Ne.symm (attacks_ne _ _ _ _ hattS)
  obtain ⟨hgeom, hclear⟩ := (mem_attacks_iff _ _ _ _).mp hattS
  have hqk : q.kind ≠ .king := by
    intro hkk
    have h1 : q = ⟨q.color, q.kind⟩ := rfl
    rw [hqc, hkk] at h1
    rw [h1] at hbS hattS
    have hk1 := king_attack_adjacent b' S e turn hattS
    cases turn with
    | white =>
      have h2 := hapart S e hbS he
      omega
    | black =>
      have h2 := hapart e S he hbS
      rw [kdist_comm] at h2
      omega
  have hSK : S ≠ kingTo turn ks := fun hh => by
    rw [hh, hbK] at hbS
    have h2 := congrArg Piece.kind (Option.some.inj hbS)
    exact hqk h2.symm
  have hS4 : S ≠ sq 4 turn.home := fun hh => by
    rw [hh, hb4] at hbS
    exact absurd hbS (by simp)
  have hSc : S ≠ sq (if ks then 7 else 0) turn.home := fun hh => by
    rw [hh, hbc] at hbS
    exact absurd hbS (by simp)
  have hbSp : p.board S = some q := by
    rw [← hchg S hS4 hSc hSK hSR]
    exact hbS
  cases hsl : isSlider q.kind with
  | false =>
    have hmem0 : e ∈ attacks p.board S q :=
      (mem_attacks_iff _ _ _ _).mpr ⟨hgeom, fun hh => by rw [hh] at hsl; exact absurd hsl (by decide)⟩
    exact hsafe' S q hbSp hqc hmem0
  | true =>
    by_cases hcp : clearPath p.board S e
    · exact hsafe' S q hbSp hqc ((mem_attacks_iff _ _ _ _).mpr ⟨hgeom, fun _ => hcp⟩)
    · have hzx : ∃ z, inSeg S e z = true ∧ p.board z ≠ none := by
        apply Classical.byContradiction
        intro hnn
        apply hcp
        intro z hzseg
        apply Classical.byContradiction
        intro hbnone
        exact hnn ⟨z, hzseg, hbnone⟩
      obtain ⟨z, hzseg, hzocc⟩ := hzx
      have hzb : b' z = none := hclear hsl z hzseg
      have hzK : z ≠ kingTo turn ks := fun hh => by
        rw [hh, hbK] at hzb
        exact absurd hzb (by simp)
      have hzR : z ≠ rookTo turn ks := fun hh => by
        rw [hh, hbR] at hzb
        exact absurd hzb (by simp)
      by_cases hz4 : z = sq 4 turn.home
      · have hseg4 : inSeg S e (sq 4 turn.home) = true := hz4 ▸ hzseg
        have hsegK : inSeg S e (kingTo turn ks) = false := by
          cases hhx : inSeg S e (kingTo turn ks) with
          | false => rfl
          | true =>
            have hn := hclear hsl _ hhx
            rw [hbK] at hn
            exact absurd hn (by simp)
        have hsegR : inSeg S e (rookTo turn ks) = false := by
          cases hhx : inSeg S e (rookTo turn ks) with
          | false => rfl
          | true =>
            have hn := hclear hsl _ hhx
            rw [hbR] at hn
            exact absurd hn (by simp)
        have heK : e ≠ kingTo turn ks := fun hh => by
          rw [hh, hbK] at he
          have h2 := congrArg Piece.color (Option.some.inj he)
          exact opp_ne_self turn h2
        have heR : e ≠ rookTo turn ks := fun hh => by
          rw [hh, hbR] at he
          have h2 := congrArg Piece.kind (Option.some.inj he)
          exact Kind.noConfusion h2
        have he4 : e ≠ sq 4 turn.home := fun hh => by
          rw [hh, hb4] at he
          exact absurd he (by simp)
        have hec : e ≠ sq (if ks then 7 else 0) turn.home := fun hh => by
          rw [hh, hbc] at he
          exact absurd he (by simp)
        exact hSR (castle_checker_geom turn ks S e
          (Bool.or_eq_true _ _ |>.mpr (Or.inl hseg4)) hsegK hsegR heK heR he4 hec hSK hS4 hSc hSe)
      · by_cases hzc : z = sq (if ks then 7 else 0) turn.home
        · have hzc2 : inSeg S e (sq (if ks then 7 else 0) turn.home) = true := hzc ▸ hzseg
          exact corner_inSeg_false S e _ (corner_if_home_fx turn ks) (corner_if_home_ry turn ks) hzc2
        · have hzr : b' z = p.board z := hchg z hz4 hzc hzK hzR
          rw [hzr] at hzb
          exact hzocc hzb

theorem eq_singleton_of_nodup {α : Type} (l : List α) (a : α) (hnd : l.Nodup) (ha : a ∈ l)
    (hall : ∀ x, x ∈ l → x = a) : l = [a] := by
  cases l with
  | nil => simp at ha
  | cons b t =>
    have hba : b = a := hall b (by simp)
    cases t with
    | nil => rw [hba]
    | cons c t =>
      have hca : c = a := hall c (by simp)
      have h0 := List.nodup_cons.mp hnd
      rw [hba, hca] at h0
      exact absurd List.mem_cons_self h0.1

theorem K3a_castle_checker (p : Pos) (m : Move) (e : Sq) (hc0 : C0 p) (hm : m ∈ legalMoves p)
    (hc : isCastle p m = true) (hg : givesCheck p m = true) (he : kingAt p p.turn.opp e) :
    checkers (play p m) e = [rookTo p.turn (castleSide m)] ∧
      e ∈ attacks (play p m).board (rookTo p.turn (castleSide m)) ⟨p.turn, .rook⟩ := by
  obtain ⟨hchg, hbK, hbR, hb4, hbc, hrookatt, hs4⟩ := castle_play_facts p m hm hc
  have hksafe : inCheck p p.turn.opp = false := hc0.safe
  have hC0P1 : C0 (play p m) := c0_play p m hc0 hm
  have hking0 : isKingMove p m = true := by
    unfold isCastle at hc
    exact (Bool.and_eq_true _ _ |>.mp hc).1
  have hksrc : p.board m.src = some ⟨p.turn, .king⟩ := kingMove_src p m hm hking0
  have hnes : e ≠ m.src := by
    intro hh
    have he2 : p.board e = some ⟨p.turn.opp, .king⟩ := he
    rw [hh, hksrc] at he2
    have h2 := congrArg Piece.color (Option.some.inj he2)
    exact opp_ne_self p.turn h2
  have heP1 : kingAt (play p m) p.turn.opp e := king_stay p m hm hksafe p.turn.opp e he hnes
  have hic0 : inCheck (play p m) p.turn.opp = true := hg
  obtain ⟨k, hkk, hattk⟩ := (inCheck_iff (play p m) p.turn.opp).mp hic0
  have hkeq : k = e := king_square_unique _ hC0P1 _ _ _ hkk heP1
  rw [hkeq, Color.opp_opp] at hattk
  obtain ⟨S, q, hbS, hqc, hattS⟩ := (attacked_iff _ _ _).mp hattk
  have hpre : ∀ S' q', p.board S' = some q' → q'.color = p.turn → e ∉ attacks p.board S' q' := by
    intro S' q' hb hq hmem
    have h1 : attacked p.board e p.turn = true := (attacked_iff _ _ _).mpr ⟨S', q', hb, hq, hmem⟩
    have h2 : inCheck p p.turn.opp = true := by
      rw [inCheck_iff]
      refine ⟨e, he, ?_⟩
      show attacked p.board e p.turn.opp.opp = true
      rw [Color.opp_opp]
      exact h1
    rw [hksafe] at h2
    exact absurd h2 (by decide)
  have hSeq : S = rookTo p.turn (castleSide m) :=
    castle_checker_aux p (play p m).board p.turn (castleSide m) e S q hC0P1.apart hpre
      hchg hbK hbR hb4 hbc heP1 hbS hqc hattS
  subst hSeq
  obtain rfl : q = ⟨p.turn, .rook⟩ := Option.some.inj (hbS.symm.trans hbR)
  have hct : (play p m).turn.opp = p.turn := by rw [play_turn, Color.opp_opp]
  have hmemR : rookTo p.turn (castleSide m) ∈ checkers (play p m) e :=
    (mem_checkers _ _ _).mpr ⟨⟨p.turn, .rook⟩, hbR, by rw [hct], hattS⟩
  have huniq : ∀ t, t ∈ checkers (play p m) e → t = rookTo p.turn (castleSide m) := by
    intro t ht
    obtain ⟨q2, hb2, hc2, ha2⟩ := (mem_checkers _ _ _).mp ht
    rw [hct] at hc2
    exact castle_checker_aux p (play p m).board p.turn (castleSide m) e t q2 hC0P1.apart hpre
      hchg hbK hbR hb4 hbc heP1 hb2 hc2 ha2
  have hnd : (checkers (play p m) e).Nodup :=
    List.Nodup.sublist List.filter_sublist nodup_allSq
  exact ⟨eq_singleton_of_nodup _ _ hnd hmemR huniq, hattS⟩

def castleGeomCheck : Bool :=
  [Color.white, Color.black].all fun c => [true, false].all fun ks => allSq.all fun e =>
    !(aligned (kingTo c ks) e && 2 ≤ kdist (kingTo c ks) e && 2 ≤ kdist (sq 4 c.home) e &&
        e != sq 4 c.home && orthLine (rookTo c ks) e && !inSeg (rookTo c ks) e (kingTo c ks)) ||
      (ry e == (c.home : Int) && inSeg (kingTo c ks) e (rookTo c ks))

set_option maxRecDepth 100000 in
theorem castleGeomCheck_true : castleGeomCheck = true := by decide +kernel

theorem K3b_castle_geom (c : Color) (ks : Bool) (e : Sq) (hal : aligned (kingTo c ks) e = true)
    (hd : 2 ≤ kdist (kingTo c ks) e) (hd0 : 2 ≤ kdist (sq 4 c.home) e) (hne : e ≠ sq 4 c.home)
    (hr : orthLine (rookTo c ks) e = true) (hnb : inSeg (rookTo c ks) e (kingTo c ks) = false) :
    ry e = c.home ∧ inSeg (kingTo c ks) e (rookTo c ks) = true := by
  have h := castleGeomCheck_true
  simp only [castleGeomCheck, List.all_eq_true] at h
  have := h c (by cases c <;> simp) ks (by cases ks <;> simp) e (mem_allSq e)
  simp_all

def CastleInv (P : Pos) (c : Color) (ks : Bool) (e : Sq) : Prop :=
  P.board (rookTo c ks) = some ⟨c, .rook⟩ ∧ kingAt P c (kingTo c ks) ∧ kingAt P c.opp e ∧
    (∃ z, inSeg (rookTo c ks) e z = true ∧ P.board z ≠ none) ∧
    (∀ z q, inSeg (rookTo c ks) e z = true → P.board z = some q → q.color = c.opp)

theorem K3_seg_quiet (P : Pos) (c : Color) (ks : Bool) (e : Sq) (hinv : CastleInv P c ks e) (hc0 : C0 P)
    (hgeom : ry e = c.home ∧ inSeg (kingTo c ks) e (rookTo c ks) = true) (z : Sq) (q : Piece)
    (hz : inSeg (rookTo c ks) e z = true) (hq : P.board z = some q) :
    kingTo c ks ∉ attacks P.board z q := by
  obtain ⟨hbR, hkk, hke, -, hcol⟩ := hinv
  obtain ⟨ryz, hzKR, hkn, hdg⟩ := castle_seg_facts c ks e z hgeom.1 hgeom.2 hz
  have hzc : q.color = c.opp := hcol z q hz hq
  intro hmem
  obtain ⟨hgeomA, hclear⟩ := (mem_attacks_iff _ _ _ _).mp hmem
  have hqq : q = ⟨q.color, q.kind⟩ := rfl
  rw [hzc] at hqq
  cases hk : q.kind with
  | pawn =>
    rw [hk] at hqq
    rw [hqq] at hq
    obtain ⟨hp0, hp7⟩ := hc0.pawns z c.opp hq
    cases c with
    | white =>
      have h0 : ry z = 0 := ryz
      exact hp0 h0
    | black =>
      have h7 : ry z = 7 := ryz
      exact hp7 h7
  | knight =>
    rw [hk] at hgeomA
    simp only [geomAttack] at hgeomA
    rw [hkn] at hgeomA
    exact absurd hgeomA (by decide)
  | bishop =>
    rw [hk] at hgeomA
    simp only [geomAttack] at hgeomA
    rw [hdg] at hgeomA
    exact absurd hgeomA (by decide)
  | rook =>
    rw [hk] at hclear
    have hnone := hclear (by decide) (rookTo c ks) hzKR
    rw [hbR] at hnone
    exact absurd hnone (by simp)
  | queen =>
    rw [hk] at hclear
    have hnone := hclear (by decide) (rookTo c ks) hzKR
    rw [hbR] at hnone
    exact absurd hnone (by simp)
  | king =>
    rw [hk] at hqq
    rw [hqq] at hq
    have hze : z = e := king_square_unique P hc0 c.opp z e hq hke
    exact (inSeg_ne hz).2 hze

theorem K3c_no_capture_rook (p : Pos) (m₀ m₁ : Move) (e : Sq) (hc0 : C0 p) (hm₀ : m₀ ∈ legalMoves p)
    (hcs : isCastle p m₀ = true) (hg₀ : givesCheck p m₀ = true) (he : kingAt p p.turn.opp e)
    (hm₁ : m₁ ∈ legalMoves (play p m₀)) (hnk : isKingMove (play p m₀) m₁ = false) :
    m₁.dst ≠ rookTo p.turn (castleSide m₀) := by
  intro hdst
  obtain ⟨hchg, hbK, hbR, hb4, hbc, hrookatt, hs4⟩ := castle_play_facts p m₀ hm₀ hcs
  obtain ⟨q, hbS1, hqc1, hmem1⟩ := legal_nonking_mem (play p m₀) m₁ hm₁ hnk
  obtain ⟨cq, kq⟩ := q
  have hpt1 : (play p m₀).turn = p.turn.opp := play_turn p m₀
  rw [hpt1] at hqc1
  have hS4 : m₁.src ≠ sq 4 p.turn.home := fun hh => by
    rw [hh, hb4] at hbS1
    exact absurd hbS1 (by simp)
  have hSc : m₁.src ≠ sq (if castleSide m₀ then 7 else 0) p.turn.home := fun hh => by
    rw [hh, hbc] at hbS1
    exact absurd hbS1 (by simp)
  have hSK : m₁.src ≠ kingTo p.turn (castleSide m₀) := fun hh => by
    rw [hh, hbK] at hbS1
    have h2 := congrArg Piece.color (Option.some.inj hbS1)
    exact opp_ne_self p.turn (h2.trans hqc1)
  have hSR : m₁.src ≠ rookTo p.turn (castleSide m₀) := fun hh => by
    rw [hh, hbR] at hbS1
    have h2 := congrArg Piece.color (Option.some.inj hbS1)
    exact opp_ne_self p.turn (h2.trans hqc1)
  have hbSp : p.board m₁.src = some ⟨cq, kq⟩ := by
    rw [← hchg m₁.src hS4 hSc hSK hSR]
    exact hbS1
  have hattR : rookTo p.turn (castleSide m₀) ∈ attacks (play p m₀).board m₁.src ⟨cq, kq⟩ := by
    rw [← hdst]
    cases kq with
    | pawn =>
      have hmem' : m₁ ∈ pawnMoves (play p m₀) m₁.src cq := hmem1
      obtain ⟨-, hdisj, -⟩ := pawnMoves_cases (play p m₀) m₁.src cq m₁ hmem'
      rcases hdisj with hd1 | hd2 | hd3
      · rw [hdst, hbR] at hd1
        exact absurd hd1.2.2 (by simp)
      · rw [hdst, hbR] at hd2
        exact absurd hd2.2.2.2.1 (by simp)
      · exact hd3.1
    | knight => exact (pieceMoves_geom _ _ _ _ hmem1 (fun he => by simp at he)).2.2
    | bishop => exact (pieceMoves_geom _ _ _ _ hmem1 (fun he => by simp at he)).2.2
    | rook => exact (pieceMoves_geom _ _ _ _ hmem1 (fun he => by simp at he)).2.2
    | queen => exact (pieceMoves_geom _ _ _ _ hmem1 (fun he => by simp at he)).2.2
    | king =>
      have hki := isKingMove_true_of_board (play p m₀) m₁ cq hbS1
      rw [hki] at hnk
      exact absurd hnk (by decide)
  obtain ⟨hgeomR, hclearR⟩ := (mem_attacks_iff _ _ _ _).mp hattR
  cases hsl : isSlider kq with
  | false =>
    have hmem0 : rookTo p.turn (castleSide m₀) ∈ attacks p.board m₁.src ⟨cq, kq⟩ :=
      (mem_attacks_iff _ _ _ _).mpr ⟨hgeomR, fun hh => by rw [hh] at hsl; exact absurd hsl (by decide)⟩
    have hatt : attacked p.board (rookTo p.turn (castleSide m₀)) p.turn.opp = true :=
      (attacked_iff _ _ _).mpr ⟨m₁.src, ⟨cq, kq⟩,hbSp, hqc1, hmem0⟩
    rw [hrookatt] at hatt
    exact absurd hatt (by decide)
  | true =>
    have hcp1 : clearPath (play p m₀).board m₁.src (rookTo p.turn (castleSide m₀)) := hclearR hsl
    by_cases hcp : clearPath p.board m₁.src (rookTo p.turn (castleSide m₀))
    · have hmem0 : rookTo p.turn (castleSide m₀) ∈ attacks p.board m₁.src ⟨cq, kq⟩ :=
        (mem_attacks_iff _ _ _ _).mpr ⟨hgeomR, fun _ => hcp⟩
      have hatt : attacked p.board (rookTo p.turn (castleSide m₀)) p.turn.opp = true :=
        (attacked_iff _ _ _).mpr ⟨m₁.src, ⟨cq, kq⟩,hbSp, hqc1, hmem0⟩
      rw [hrookatt] at hatt
      exact absurd hatt (by decide)
    · have hzx : ∃ z, inSeg m₁.src (rookTo p.turn (castleSide m₀)) z = true ∧ p.board z ≠ none := by
        apply Classical.byContradiction
        intro hnn
        apply hcp
        intro z hzseg
        apply Classical.byContradiction
        intro hbnone
        exact hnn ⟨z, hzseg, hbnone⟩
      obtain ⟨z, hzseg, hzocc⟩ := hzx
      have hzb : (play p m₀).board z = none := hcp1 z hzseg
      have hzK : z ≠ kingTo p.turn (castleSide m₀) := fun hh => by
        rw [hh, hbK] at hzb
        exact absurd hzb (by simp)
      have hzR : z ≠ rookTo p.turn (castleSide m₀) := (inSeg_ne hzseg).2
      by_cases hz4 : z = sq 4 p.turn.home
      · have hseg4 : inSeg m₁.src (rookTo p.turn (castleSide m₀)) (sq 4 p.turn.home) = true :=
          hz4 ▸ hzseg
        have hgeom4 : geomAttack cq kq m₁.src (sq 4 p.turn.home) = true :=
          geomAttack_seg cq kq m₁.src _ _ hsl hseg4 hgeomR
        have hcp4 : clearPath p.board m₁.src (sq 4 p.turn.home) := by
          intro w hw
          have hwR : inSeg m₁.src (rookTo p.turn (castleSide m₀)) w = true :=
            inSeg_trans _ _ _ _ hseg4 hw
          have hwP1 : (play p m₀).board w = none := hcp1 w hwR
          by_cases hw4 : w = sq 4 p.turn.home
          · exact absurd hw4 (inSeg_ne hw).2
          · by_cases hwc : w = sq (if castleSide m₀ then 7 else 0) p.turn.home
            · subst hwc
              exact False.elim (corner_inSeg_false m₁.src _ _ (corner_if_home_fx p.turn (castleSide m₀))
                (corner_if_home_ry p.turn (castleSide m₀)) hwR)
            · by_cases hwK : w = kingTo p.turn (castleSide m₀)
              · rw [hwK, hbK] at hwP1
                exact absurd hwP1 (by simp)
              · by_cases hwR2 : w = rookTo p.turn (castleSide m₀)
                · exact absurd hwR2 (inSeg_ne hwR).2
                · have hwb := hchg w hw4 hwc hwK hwR2
                  rw [hwb] at hwP1
                  exact hwP1
        have hmem4 : sq 4 p.turn.home ∈ attacks p.board m₁.src ⟨cq, kq⟩ :=
          (mem_attacks_iff _ _ _ _).mpr ⟨hgeom4, fun _ => hcp4⟩
        have hatt : attacked p.board (sq 4 p.turn.home) p.turn.opp = true :=
          (attacked_iff _ _ _).mpr ⟨m₁.src, ⟨cq, kq⟩,hbSp, hqc1, hmem4⟩
        rw [hs4] at hatt
        exact absurd hatt (by decide)
      · by_cases hzc : z = sq (if castleSide m₀ then 7 else 0) p.turn.home
        · subst hzc
          exact corner_inSeg_false m₁.src _ _ (corner_if_home_fx p.turn (castleSide m₀))
            (corner_if_home_ry p.turn (castleSide m₀)) hzseg
        · have hzr := hchg z hz4 hzc hzK hzR
          rw [hzr] at hzb
          exact hzocc hzb

theorem K3c_lands_in_seg (p : Pos) (m₀ m₁ : Move) (e : Sq) (hc0 : C0 p) (hm₀ : m₀ ∈ legalMoves p)
    (hcs : isCastle p m₀ = true) (hg₀ : givesCheck p m₀ = true) (he : kingAt p p.turn.opp e)
    (hm₁ : m₁ ∈ legalMoves (play p m₀)) (hnk : isKingMove (play p m₀) m₁ = false) :
    inSeg (rookTo p.turn (castleSide m₀)) e m₁.dst = true ∧ epVictim (play p m₀) m₁ = none := by
  obtain ⟨hchk1, -⟩ := K3a_castle_checker p m₀ e hc0 hm₀ hcs hg₀ he
  have hC0P1 : C0 (play p m₀) := c0_play p m₀ hc0 hm₀
  have hking0 : isKingMove p m₀ = true := by
    have h2 := hcs
    unfold isCastle at h2
    exact (Bool.and_eq_true _ _ |>.mp h2).1
  have hksrc : p.board m₀.src = some ⟨p.turn, .king⟩ := kingMove_src p m₀ hm₀ hking0
  have hnes : e ≠ m₀.src := by
    intro hh
    have he2 : p.board e = some ⟨p.turn.opp, .king⟩ := he
    rw [hh, hksrc] at he2
    have h2 := congrArg Piece.color (Option.some.inj he2)
    exact opp_ne_self p.turn h2
  have heP1 : kingAt (play p m₀) p.turn.opp e := king_stay p m₀ hm₀ hc0.safe p.turn.opp e he hnes
  have hke1 : kingAt (play p m₀) (play p m₀).turn e := by rw [play_turn]; exact heP1
  have hany : ((p.board m₀.src).any fun q => q.kind == .pawn) = false := by rw [hksrc]; rfl
  have hep0 : (play p m₀).ep = none := by
    rw [play_ep, hany, Bool.false_and]
    rfl
  have heV : ∀ v, epVictim (play p m₀) m₁ ≠ some v := by
    intro v hv
    obtain ⟨hepE, -⟩ := epVictim_spec (play p m₀) m₁ v hm₁ hv
    rw [hep0] at hepE
    exact absurd hepE (by simp)
  constructor
  · obtain h := lemmaE_single (play p m₀) e (rookTo p.turn (castleSide m₀)) hC0P1 hke1 hchk1 m₁ hm₁ hnk
    rcases h with hd | hep | hseg
    · exact absurd hd (K3c_no_capture_rook p m₀ m₁ e hc0 hm₀ hcs hg₀ he hm₁ hnk)
    · exact absurd hep (heV _)
    · exact hseg
  · cases hv : epVictim (play p m₀) m₁ with
    | none => rfl
    | some v => exact absurd hv (heV v)

theorem K3c_reply (p : Pos) (m₀ m₁ : Move) (e : Sq) (hc0 : C0 p) (hm₀ : m₀ ∈ legalMoves p)
    (hcs : isCastle p m₀ = true) (hg₀ : givesCheck p m₀ = true) (he : kingAt p p.turn.opp e)
    (hgeom : ry e = p.turn.home ∧ inSeg (kingTo p.turn (castleSide m₀)) e (rookTo p.turn (castleSide m₀)) = true)
    (hm₁ : m₁ ∈ legalMoves (play p m₀)) (hnk : isKingMove (play p m₀) m₁ = false) :
    CastleInv (play (play p m₀) m₁) p.turn (castleSide m₀) e := by
  obtain ⟨hchk1, hatt2⟩ := K3a_castle_checker p m₀ e hc0 hm₀ hcs hg₀ he
  obtain ⟨hgseg, hepV⟩ := K3c_lands_in_seg p m₀ m₁ e hc0 hm₀ hcs hg₀ he hm₁ hnk
  have hncap := K3c_no_capture_rook p m₀ m₁ e hc0 hm₀ hcs hg₀ he hm₁ hnk
  obtain ⟨-, hbK, hbR, -, -, -, -⟩ := castle_play_facts p m₀ hm₀ hcs
  have hC0P1 : C0 (play p m₀) := c0_play p m₀ hc0 hm₀
  have hsafe1 : inCheck (play p m₀) (play p m₀).turn.opp = false := hC0P1.safe
  obtain ⟨q, hbS1, hqc1, hmem1⟩ := legal_nonking_mem (play p m₀) m₁ hm₁ hnk
  rw [play_turn] at hqc1
  have hsd : m₁.src ≠ m₁.dst := legal_src_ne_dst _ _ hm₁
  have hcast1 : isCastle (play p m₀) m₁ = false := by
    unfold isCastle
    rw [hnk, Bool.false_and]
  have hsrcR : rookTo p.turn (castleSide m₀) ≠ m₁.src := by
    intro hh
    rw [← hh, hbR] at hbS1
    have h2 := congrArg Piece.color (Option.some.inj hbS1)
    exact opp_ne_self p.turn (h2.trans hqc1)
  have hepR : epVictim (play p m₀) m₁ ≠ some (rookTo p.turn (castleSide m₀)) := by
    rw [hepV]
    simp
  have hboardR : (play (play p m₀) m₁).board (rookTo p.turn (castleSide m₀)) = some ⟨p.turn, .rook⟩ := by
    rw [play_board_other (play p m₀) m₁ _ hsrcR (Ne.symm hncap) hepR hcast1]
    exact hbR
  have hkk1 : kingAt (play p m₀) p.turn (kingTo p.turn (castleSide m₀)) := hbK
  have hkk2 : kingAt (play (play p m₀) m₁) p.turn (kingTo p.turn (castleSide m₀)) :=
    (kingAt_play_nonking (play p m₀) m₁ hm₁ hnk hsafe1 p.turn _).mpr hkk1
  have hking0 : isKingMove p m₀ = true := by
    have h2 := hcs
    unfold isCastle at h2
    exact (Bool.and_eq_true _ _ |>.mp h2).1
  have hksrc : p.board m₀.src = some ⟨p.turn, .king⟩ := kingMove_src p m₀ hm₀ hking0
  have hnes : e ≠ m₀.src := by
    intro hh
    have he2 : p.board e = some ⟨p.turn.opp, .king⟩ := he
    rw [hh, hksrc] at he2
    have h2 := congrArg Piece.color (Option.some.inj he2)
    exact opp_ne_self p.turn h2
  have heP1 : kingAt (play p m₀) p.turn.opp e := king_stay p m₀ hm₀ hc0.safe p.turn.opp e he hnes
  have heP2 : kingAt (play (play p m₀) m₁) p.turn.opp e :=
    (kingAt_play_nonking (play p m₀) m₁ hm₁ hnk hsafe1 p.turn.opp e).mpr heP1
  obtain ⟨-, hclear⟩ := (mem_attacks_iff (play p m₀).board (rookTo p.turn (castleSide m₀)) e
    ⟨p.turn, .rook⟩).mp hatt2
  have hcp1 : clearPath (play p m₀).board (rookTo p.turn (castleSide m₀)) e :=
    hclear (by show isSlider Kind.rook = true; decide)
  refine ⟨hboardR, hkk2, heP2, ⟨m₁.dst, hgseg, ?_⟩, ?_⟩
  · rw [play_board_dst]
    cases m₁.promo with
    | none => rw [hbS1]; simp
    | some k => rw [hbS1]; simp
  · intro z q2 hz hq2
    by_cases hzd : z = m₁.dst
    · subst hzd
      rw [play_board_dst] at hq2
      cases hpm : m₁.promo with
      | none =>
        rw [hpm] at hq2
        dsimp only [] at hq2
        rw [hbS1] at hq2
        have hqq := Option.some.inj hq2
        rw [← hqq]
        exact hqc1
      | some k =>
        rw [hpm] at hq2
        dsimp only [] at hq2
        rw [hbS1] at hq2
        rw [Option.map_some] at hq2
        have hqq := Option.some.inj hq2
        rw [← hqq]
        exact hqc1
    · by_cases hzs : z = m₁.src
      · subst hzs
        rw [play_board_src _ _ hsd] at hq2
        exact absurd hq2 (by simp)
      · have hze : epVictim (play p m₀) m₁ ≠ some z := by rw [hepV]; simp
        have hbz := play_board_other (play p m₀) m₁ z hzs hzd hze hcast1
        rw [hbz] at hq2
        rw [hcp1 z hz] at hq2
        exact absurd hq2 (by simp)

def k3dSegHomeCheck : Bool :=
  [Color.white, Color.black].all fun c => [true, false].all fun ks => allSq.all fun e =>
    allSq.all fun z =>
      !((ry e == (c.home : Int)) && inSeg (rookTo c ks) e z) || (ry z == (c.home : Int))

set_option maxRecDepth 100000 in
theorem k3dSegHomeCheck_true : k3dSegHomeCheck = true := by decide +kernel

theorem k3_ry_rookTo (c : Color) (ks : Bool) : ry (rookTo c ks) = (c.home : Int) := by
  unfold rookTo
  rw [ry_sq _ _ (by cases ks <;> decide) (home_lt _)]

theorem k3_ry_kingTo (c : Color) (ks : Bool) : ry (kingTo c ks) = (c.home : Int) := by
  unfold kingTo
  rw [ry_sq _ _ (by cases ks <;> decide) (home_lt _)]

theorem k3_seg_home (c : Color) (ks : Bool) (e z : Sq) (he : ry e = (c.home : Int))
    (hz : inSeg (rookTo c ks) e z = true) : ry z = (c.home : Int) := by
  have h := k3dSegHomeCheck_true
  simp only [k3dSegHomeCheck, List.all_eq_true] at h
  have h2 := h c (by cases c <;> simp) ks (by cases ks <;> simp) e (mem_allSq e) z (mem_allSq z)
  have hpre : ((ry e == (c.home : Int)) && inSeg (rookTo c ks) e z) = true := by
    rw [beq_iff_eq.mpr he, hz]
    rfl
  rw [hpre, Bool.not_true, Bool.false_or] at h2
  exact beq_iff_eq.mp h2

def k3dSegRookCheck : Bool :=
  [Color.white, Color.black].all fun c => [true, false].all fun ks => allSq.all fun e =>
    allSq.all fun w => allSq.all fun x =>
      !((ry e == (c.home : Int)) && inSeg (kingTo c ks) e (rookTo c ks) &&
          inSeg (rookTo c ks) e w && inSeg x (kingTo c ks) w) ||
        inSeg x (kingTo c ks) (rookTo c ks)

set_option maxRecDepth 100000 in
theorem k3dSegRookCheck_true : k3dSegRookCheck = true := by decide +kernel

theorem k3d_seg_rook (c : Color) (ks : Bool) (e w x : Sq) (he : ry e = (c.home : Int))
    (hKR : inSeg (kingTo c ks) e (rookTo c ks) = true) (hRw : inSeg (rookTo c ks) e w = true)
    (hxw : inSeg x (kingTo c ks) w = true) : inSeg x (kingTo c ks) (rookTo c ks) = true := by
  have h := k3dSegRookCheck_true
  simp only [k3dSegRookCheck, List.all_eq_true] at h
  have h2 := h c (by cases c <;> simp) ks (by cases ks <;> simp) e (mem_allSq e) w (mem_allSq w)
    x (mem_allSq x)
  have hpre : ((ry e == (c.home : Int)) && inSeg (kingTo c ks) e (rookTo c ks) &&
      inSeg (rookTo c ks) e w && inSeg x (kingTo c ks) w) = true := by
    rw [beq_iff_eq.mpr he, hKR, hRw, hxw]
    rfl
  rw [hpre, Bool.not_true, Bool.false_or] at h2
  exact h2

def k3dDiscCheck : Bool :=
  [Color.white, Color.black].all fun c => [true, false].all fun ks => allSq.all fun e =>
    allSq.all fun s =>
      !((ry e == (c.home : Int)) && inSeg (kingTo c ks) e (rookTo c ks) &&
          inSeg s e (rookTo c ks)) ||
        ((s == kingTo c ks) || inSeg s e (kingTo c ks))

set_option maxRecDepth 100000 in
theorem k3dDiscCheck_true : k3dDiscCheck = true := by decide +kernel

theorem k3d_disc (c : Color) (ks : Bool) (e s : Sq) (he : ry e = (c.home : Int))
    (hKR : inSeg (kingTo c ks) e (rookTo c ks) = true) (hsR : inSeg s e (rookTo c ks) = true) :
    s = kingTo c ks ∨ inSeg s e (kingTo c ks) = true := by
  have h := k3dDiscCheck_true
  simp only [k3dDiscCheck, List.all_eq_true] at h
  have h2 := h c (by cases c <;> simp) ks (by cases ks <;> simp) e (mem_allSq e) s (mem_allSq s)
  have hpre : ((ry e == (c.home : Int)) && inSeg (kingTo c ks) e (rookTo c ks) &&
      inSeg s e (rookTo c ks)) = true := by
    rw [beq_iff_eq.mpr he, hKR, hsR]
    rfl
  rw [hpre, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h2
  exact h2

def k3dRookMoveCheck : Bool :=
  [Color.white, Color.black].all fun c => [true, false].all fun ks => allSq.all fun e =>
    allSq.all fun t =>
      !((ry e == (c.home : Int)) && inSeg (kingTo c ks) e (rookTo c ks) && orthLine t e &&
          orthLine (rookTo c ks) t && !inSeg (rookTo c ks) e t && t != e && t != kingTo c ks &&
          t != rookTo c ks) ||
        (inSeg (rookTo c ks) t e || inSeg (rookTo c ks) t (kingTo c ks))

set_option maxRecDepth 100000 in
theorem k3dRookMoveCheck_true : k3dRookMoveCheck = true := by decide +kernel

theorem k3d_rook_move (c : Color) (ks : Bool) (e t : Sq) (he : ry e = (c.home : Int))
    (hKR : inSeg (kingTo c ks) e (rookTo c ks) = true) (ho1 : orthLine t e = true)
    (ho2 : orthLine (rookTo c ks) t = true) (hnb : inSeg (rookTo c ks) e t = false)
    (hne : t ≠ e) (hnK : t ≠ kingTo c ks) (hnR : t ≠ rookTo c ks) :
    inSeg (rookTo c ks) t e = true ∨ inSeg (rookTo c ks) t (kingTo c ks) = true := by
  have h := k3dRookMoveCheck_true
  simp only [k3dRookMoveCheck, List.all_eq_true] at h
  have h2 := h c (by cases c <;> simp) ks (by cases ks <;> simp) e (mem_allSq e) t (mem_allSq t)
  have b5 : (!inSeg (rookTo c ks) e t) = true := by rw [hnb]; rfl
  have hpre : ((ry e == (c.home : Int)) && inSeg (kingTo c ks) e (rookTo c ks) && orthLine t e &&
      orthLine (rookTo c ks) t && !inSeg (rookTo c ks) e t && t != e && t != kingTo c ks &&
      t != rookTo c ks) = true := by
    rw [beq_iff_eq.mpr he, hKR, ho1, ho2, b5, bne_iff_ne.mpr hne, bne_iff_ne.mpr hnK,
      bne_iff_ne.mpr hnR]
    rfl
  rw [hpre, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h2
  exact h2

theorem k3d_checkers_single (P : Pos) (k : Sq) (hc0 : C0 P) (hk : kingAt P P.turn k)
    (hchk : inCheck P P.turn = true) (m : Move) (hm : m ∈ legalMoves P)
    (hnk : isKingMove P m = false) : ∃ χ, checkers P k = [χ] := by
  have huniq : ∀ s, kingAt P P.turn s → s = k := fun s hs => king_square_unique P hc0 P.turn s k hs hk
  have hne' : checkers P k ≠ [] := (inCheck_iff_checkers P k hk huniq).mp hchk
  have hle := checkers_le_one_of_nonking P k hc0 hk m hm hnk
  match hcl : checkers P k with
  | [] => exact absurd hcl hne'
  | [χ] => exact ⟨χ, rfl⟩
  | _ :: _ :: rest =>
    exfalso
    rw [hcl] at hle
    simp only [List.length_cons] at hle
    omega

theorem k3d_victim_not_in_seg (P : Pos) (c : Color) (ks : Bool) (e z : Sq) (hc0 : C0 P)
    (he : ry e = (c.home : Int)) (hz : inSeg (rookTo c ks) e z = true) (m : Move)
    (hm : m ∈ legalMoves P) (hv : epVictim P m = some z) : False := by
  obtain ⟨-, -, hbv, -, -, -⟩ := epVictim_spec P m z hm hv
  obtain ⟨hp0, hp7⟩ := hc0.pawns z P.turn.opp hbv
  have hryz : ry z = (c.home : Int) := k3_seg_home c ks e z he hz
  cases c with
  | white => exact hp0 hryz
  | black => exact hp7 hryz

theorem K3d_own_dst_outside (P : Pos) (c : Color) (ks : Bool) (e : Sq) (hinv : CastleInv P c ks e)
    (hc0 : C0 P) (hgeom : ry e = c.home ∧ inSeg (kingTo c ks) e (rookTo c ks) = true) (hturn : P.turn = c)
    (hchk : inCheck P P.turn = true) (m : Move) (hm : m ∈ legalMoves P) (hnk : isKingMove P m = false) :
    inSeg (rookTo c ks) e m.dst = false ∧ m.dst ≠ e := by
  have hkKt : kingAt P P.turn (kingTo c ks) := by rw [hturn]; exact hinv.2.1
  obtain ⟨χ, hχ⟩ := k3d_checkers_single P (kingTo c ks) hc0 hkKt hchk m hm hnk
  have hχmem : χ ∈ checkers P (kingTo c ks) := by rw [hχ]; exact List.mem_cons_self
  have hdstne : m.dst ≠ e := fun hde => legal_not_capture_king P m hm hc0.safe c.opp (hde ▸ hinv.2.2.1)
  refine ⟨?_, hdstne⟩
  cases hsg : inSeg (rookTo c ks) e m.dst with
  | false => rfl
  | true =>
    exfalso
    obtain hle := lemmaE_single P (kingTo c ks) χ hc0 hkKt hχ m hm hnk
    rcases hle with hd | hep | hs3
    · obtain ⟨q', hq', -, hatt'⟩ := (mem_checkers P (kingTo c ks) χ).mp hχmem
      have hχseg : inSeg (rookTo c ks) e χ = true := hd ▸ hsg
      exact K3_seg_quiet P c ks e hinv hc0 hgeom χ q' hχseg hq' hatt'
    · obtain ⟨-, -, hbv, hfv, hrv, hsrcp⟩ := epVictim_spec P m χ hm hep
      rw [hturn] at hbv
      obtain ⟨q', hq', -, hatt'⟩ := (mem_checkers P (kingTo c ks) χ).mp hχmem
      have hqp : q' = ⟨c.opp, .pawn⟩ := Option.some.inj (hq'.symm.trans hbv)
      subst hqp
      obtain ⟨hpa1, -⟩ := pawn_attack_geom P.board χ (kingTo c ks) c.opp hatt'
      obtain ⟨q0, hq0, -, hmem0⟩ := legal_nonking_mem P m hm hnk
      have hq0p : q0 = ⟨P.turn, .pawn⟩ := Option.some.inj (hq0.symm.trans hsrcp)
      subst hq0p
      have hmem2 : m ∈ pawnMoves P m.src P.turn := hmem0
      obtain ⟨-, hdisj, -⟩ := pawnMoves_cases P m.src P.turn m hmem2
      have hrydst : ry m.dst = (c.home : Int) := k3_seg_home c ks e m.dst hgeom.1 hsg
      have hryK : ry (kingTo c ks) = (c.home : Int) := k3_ry_kingTo c ks
      rcases hdisj with hd1 | hd2 | hd3
      · obtain ⟨-, hryd, -⟩ := hd1
        rw [hturn] at hryd
        rcases color_fwd_cases c with ⟨hf1, hf2⟩ | ⟨hf1, hf2⟩ <;> omega
      · obtain ⟨-, hryd, -⟩ := hd2
        rw [hturn] at hryd
        rcases color_fwd_cases c with ⟨hf1, hf2⟩ | ⟨hf1, hf2⟩ <;> omega
      · obtain ⟨hattd, -⟩ := hd3
        obtain ⟨hryd, -⟩ := pawn_attack_geom P.board m.src m.dst P.turn hattd
        rw [hturn] at hryd
        rcases color_fwd_cases c with ⟨hf1, hf2⟩ | ⟨hf1, hf2⟩ <;> omega
    · have hsegR : inSeg χ (kingTo c ks) (rookTo c ks) = true :=
        k3d_seg_rook c ks e m.dst χ hgeom.1 hgeom.2 hsg hs3
      have h0 := checker_seg_empty P (kingTo c ks) χ (rookTo c ks) hχmem hsegR
      rw [hinv.1] at h0
      exact absurd h0 (by simp)

theorem K3d_own_rook_stays (P : Pos) (c : Color) (ks : Bool) (e : Sq) (hinv : CastleInv P c ks e)
    (hc0 : C0 P) (hgeom : ry e = c.home ∧ inSeg (kingTo c ks) e (rookTo c ks) = true) (hturn : P.turn = c)
    (hchk : inCheck P P.turn = true) (m : Move) (hm : m ∈ legalMoves P) (hnk : isKingMove P m = false)
    (hg : givesCheck P m = true) : m.src ≠ rookTo c ks := by
  obtain ⟨hout, hdne⟩ := K3d_own_dst_outside P c ks e hinv hc0 hgeom hturn hchk m hm hnk
  intro hsrc
  have hsd : m.src ≠ m.dst := legal_src_ne_dst P m hm
  have hepv : epVictim P m = none := by
    cases hv : epVictim P m with
    | none => rfl
    | some v =>
      obtain ⟨-, -, -, -, -, hsrcp⟩ := epVictim_spec P m v hm hv
      rw [hsrc, hinv.1] at hsrcp
      simp only [Option.some.injEq, Piece.mk.injEq] at hsrcp
      exact absurd hsrcp.2 (by decide)
  have hkK' : kingAt (play P m) c (kingTo c ks) :=
    (kingAt_play_nonking P m hm hnk hc0.safe c _).mpr hinv.2.1
  have hke' : kingAt (play P m) c.opp e :=
    (kingAt_play_nonking P m hm hnk hc0.safe c.opp e).mpr hinv.2.2.1
  have hic : inCheck (play P m) c.opp = true := by
    unfold givesCheck at hg
    rw [hturn] at hg
    exact hg
  obtain ⟨k, hkk, hattk⟩ := (inCheck_iff (play P m) c.opp).mp hic
  have hkeq : k = e := king_square_unique _ (c0_play P m hc0 hm) c.opp _ _ hkk hke'
  rw [hkeq, Color.opp_opp] at hattk
  obtain ⟨S, q, hbS, hqc, hattS⟩ := (attacked_iff _ _ _).mp hattk
  obtain ⟨hgeoS, hclearS⟩ := (mem_attacks_iff _ _ _ _).mp hattS
  obtain ⟨q0, hq0, -, hmem0⟩ := legal_nonking_mem P m hm hnk
  have hq0r : q0 = ⟨c, .rook⟩ := Option.some.inj ((hsrc ▸ hq0).symm.trans hinv.1)
  obtain ⟨-, hpr, hattmv⟩ := mem_pieceMoves_nonpawn P m.src q0 m hmem0
    (by rw [hq0r]; exact fun h => Kind.noConfusion h)
  rw [hq0r, hsrc] at hattmv
  obtain ⟨hgmv, hcmv⟩ := (mem_attacks_iff _ _ _ _).mp hattmv
  have hcpRo : clearPath P.board (rookTo c ks) m.dst := hcmv (by show isSlider Kind.rook = true; decide)
  have hoRt : orthLine (rookTo c ks) m.dst = true := hgmv
  have hbdst : (play P m).board m.dst = some ⟨c, .rook⟩ := by
    rw [play_board_dst, hpr, hsrc]
    exact hinv.1
  have hSsrc : S ≠ m.src := fun hh => by
    rw [hh, play_board_src P m hsd] at hbS
    exact absurd hbS (by simp)
  by_cases hqk : q.kind = .king
  · have hqq : q = ⟨c, .king⟩ := by
      obtain ⟨cc, kk⟩ := q
      show (⟨cc, kk⟩ : Piece) = ⟨c, .king⟩
      simp only [Piece.mk.injEq]
      exact ⟨hqc, hqk⟩
    rw [hqq] at hbS hattS
    have hSk : S = kingTo c ks := king_square_unique _ (c0_play P m hc0 hm) c S _ hbS hkK'
    have hk1 := king_attack_adjacent _ S e c hattS
    rw [hSk] at hk1
    cases c with
    | white =>
      have h2 := hc0.apart (kingTo .white ks) e hinv.2.1 hinv.2.2.1
      omega
    | black =>
      have h2 := hc0.apart e (kingTo .black ks) hinv.2.2.1 hinv.2.1
      rw [kdist_comm] at h2
      omega
  · by_cases hSd : S = m.dst
    · subst hSd
      have hqR : q = ⟨c, .rook⟩ := Option.some.inj (hbS.symm.trans hbdst)
      subst hqR
      have ho1 : orthLine m.dst e = true := hgeoS
      have hdstR : m.dst ≠ rookTo c ks := fun hh => hsd (hsrc.trans hh.symm)
      have hdstK : m.dst ≠ kingTo c ks := fun hh => by
        rw [hh] at hbdst
        have h2 := Option.some.inj (hbdst.symm.trans hkK')
        exact Kind.noConfusion (congrArg Piece.kind h2)
      obtain hdz | hdz := k3d_rook_move c ks e m.dst hgeom.1 hgeom.2 ho1 hoRt hout hdne hdstK hdstR
      · have h0 := hcpRo e hdz
        rw [hinv.2.2.1] at h0
        exact absurd h0 (by simp)
      · have h0 := hcpRo _ hdz
        rw [hinv.2.1] at h0
        exact absurd h0 (by simp)
    · have hSev : epVictim P m ≠ some S := by rw [hepv]; simp
      have hbSp : P.board S = some q := by
        rw [← nonking_board_change P m hm hnk S hSsrc hSd hSev]
        exact hbS
      have hcontra : e ∈ attacks P.board S q → False := fun hmemP => by
        have hattP : attacked P.board e c = true := (attacked_iff _ _ _).mpr ⟨S, q, hbSp, hqc, hmemP⟩
        have hic0 : inCheck P c.opp = true := by
          rw [inCheck_iff]
          exact ⟨e, hinv.2.2.1, by rw [Color.opp_opp]; exact hattP⟩
        rw [← hturn] at hic0
        rw [hc0.safe] at hic0
        exact absurd hic0 (by decide)
      cases hsl : isSlider q.kind with
      | false =>
        exact hcontra ((mem_attacks_iff _ _ _ _).mpr
          ⟨hgeoS, fun hh => by rw [hh] at hsl; exact absurd hsl (by decide)⟩)
      | true =>
        have hclearplay : clearPath (play P m).board S e := hclearS hsl
        have hSRf : inSeg S e (rookTo c ks) = false := by
          cases hh : inSeg S e (rookTo c ks) with
          | false => rfl
          | true =>
            exfalso
            obtain hSK | hsegK := k3d_disc c ks e S hgeom.1 hgeom.2 hh
            · rw [hSK] at hbS
              have hqq : q = ⟨c, .king⟩ := Option.some.inj (hbS.symm.trans hkK')
              rw [hqq] at hqk
              exact hqk rfl
            · have h0 := hclearplay _ hsegK
              rw [hkK'] at h0
              exact absurd h0 (by simp)
        have hcp : clearPath P.board S e := by
          intro z hz
          have hzP : (play P m).board z = none := hclearplay z hz
          by_cases hzd : z = m.dst
          · rw [hzd, hbdst] at hzP
            exact absurd hzP (by simp)
          · by_cases hzs : z = m.src
            · rw [hzs, hsrc] at hz
              rw [hz] at hSRf
              exact absurd hSRf (by decide)
            · have hzv : epVictim P m ≠ some z := by rw [hepv]; simp
              rw [nonking_board_change P m hm hnk z hzs hzd hzv] at hzP
              exact hzP
        exact hcontra ((mem_attacks_iff _ _ _ _).mpr ⟨hgeoS, fun _ => hcp⟩)

theorem K3d_step_own (P : Pos) (c : Color) (ks : Bool) (e : Sq) (hinv : CastleInv P c ks e) (hc0 : C0 P)
    (hgeom : ry e = c.home ∧ inSeg (kingTo c ks) e (rookTo c ks) = true) (hturn : P.turn = c)
    (hchk : inCheck P P.turn = true) (m : Move) (hm : m ∈ legalMoves P) (hnk : isKingMove P m = false)
    (hg : givesCheck P m = true) : CastleInv (play P m) c ks e := by
  obtain ⟨hout, hdne⟩ := K3d_own_dst_outside P c ks e hinv hc0 hgeom hturn hchk m hm hnk
  have hsrcR := K3d_own_rook_stays P c ks e hinv hc0 hgeom hturn hchk m hm hnk hg
  have hsd : m.src ≠ m.dst := legal_src_ne_dst P m hm
  obtain ⟨q0, hq0, hqc0, -⟩ := legal_nonking_mem P m hm hnk
  rw [hturn] at hqc0
  have hdstR : m.dst ≠ rookTo c ks := fun hh => by
    have hq2 : P.board m.dst = some ⟨c, .rook⟩ := hh ▸ hinv.1
    have h3 := legal_dst_not_own P m hm _ hq2
    exact h3 hturn.symm
  have hevR : epVictim P m ≠ some (rookTo c ks) := by
    intro hv
    obtain ⟨-, -, hbv, -, -, -⟩ := epVictim_spec P m _ hm hv
    rw [hinv.1] at hbv
    simp only [Option.some.injEq, Piece.mk.injEq] at hbv
    exact absurd hbv.2 (by decide)
  have hbR' : (play P m).board (rookTo c ks) = some ⟨c, .rook⟩ := by
    rw [nonking_board_change P m hm hnk _ (Ne.symm hsrcR) (Ne.symm hdstR) hevR]
    exact hinv.1
  have hkK' : kingAt (play P m) c (kingTo c ks) :=
    (kingAt_play_nonking P m hm hnk hc0.safe c _).mpr hinv.2.1
  have hke' : kingAt (play P m) c.opp e :=
    (kingAt_play_nonking P m hm hnk hc0.safe c.opp e).mpr hinv.2.2.1
  obtain ⟨z0, hz0, hz0occ⟩ := hinv.2.2.2.1
  have hq00 : ∃ q, P.board z0 = some q := by
    cases hb : P.board z0 with
    | none => exact absurd hb hz0occ
    | some q => exact ⟨q, rfl⟩
  obtain ⟨q00, hq00⟩ := hq00
  have hq00c : q00.color = c.opp := hinv.2.2.2.2 z0 q00 hz0 hq00
  have hnon : ∃ z, inSeg (rookTo c ks) e z = true ∧ (play P m).board z ≠ none := by
    refine ⟨z0, hz0, ?_⟩
    intro h0
    have hzdst : z0 ≠ m.dst := fun hh => by
      have hzP2 : (play P m).board m.dst ≠ none := by
        rw [play_board_dst]
        cases hp : m.promo with
        | none => rw [hq0]; simp
        | some kk => rw [hq0]; simp
      rw [hh] at h0
      exact hzP2 h0
    have hzsrc : z0 ≠ m.src := fun hh => by
      rw [hh] at hq00
      have h2 := Option.some.inj (hq00.symm.trans hq0)
      rw [← h2] at hqc0
      exact opp_ne_self c (hqc0.symm.trans hq00c)
    have hzv : epVictim P m ≠ some z0 := fun hv =>
      k3d_victim_not_in_seg P c ks e z0 hc0 hgeom.1 hz0 m hm hv
    rw [nonking_board_change P m hm hnk z0 hzsrc hzdst hzv] at h0
    exact hz0occ h0
  have hcols : ∀ z q, inSeg (rookTo c ks) e z = true → (play P m).board z = some q →
      q.color = c.opp := by
    intro z q hz hq
    by_cases hzd : z = m.dst
    · rw [hzd] at hz
      rw [hz] at hout
      exact absurd hout (by decide)
    · by_cases hzs : z = m.src
      · subst hzs
        rw [play_board_src P m hsd] at hq
        exact absurd hq (by simp)
      · have hzv : epVictim P m ≠ some z := by
          intro hv
          have hze : (play P m).board z = none := by
            have hvd : z ≠ m.dst := hzd
            exact play_board_epVictim P m z hv hvd
          rw [hze] at hq
          exact absurd hq (by simp)
        rw [nonking_board_change P m hm hnk z hzs hzd hzv] at hq
        exact hinv.2.2.2.2 z q hz hq
  exact ⟨hbR', hkK', hke', hnon, hcols⟩

theorem K3d_opp_rook_safe (P : Pos) (c : Color) (ks : Bool) (e : Sq) (hinv : CastleInv P c ks e)
    (hc0 : C0 P) (hgeom : ry e = c.home ∧ inSeg (kingTo c ks) e (rookTo c ks) = true) (hturn : P.turn = c.opp)
    (hchk : inCheck P P.turn = true) (m : Move) (hm : m ∈ legalMoves P) (hnk : isKingMove P m = false) :
    m.dst ≠ rookTo c ks := by
  have hkeT : kingAt P P.turn e := by rw [hturn]; exact hinv.2.2.1
  obtain ⟨χ, hχ⟩ := k3d_checkers_single P e hc0 hkeT hchk m hm hnk
  have hχmem : χ ∈ checkers P e := by rw [hχ]; exact List.mem_cons_self
  intro hdst
  obtain hle := lemmaE_single P e χ hc0 hkeT hχ m hm hnk
  rcases hle with hd | hep | hs3
  · obtain ⟨z0, hz0, hz0occ⟩ := hinv.2.2.2.1
    have hχR : χ = rookTo c ks := hd.symm.trans hdst
    have h0 := checker_seg_empty P e χ z0 hχmem (hχR ▸ hz0)
    exact hz0occ h0
  · obtain ⟨-, hbdst, -⟩ := epVictim_spec P m χ hm hep
    rw [hdst, hinv.1] at hbdst
    exact absurd hbdst (by simp)
  · have hseg : inSeg χ e (rookTo c ks) = true := hdst ▸ hs3
    have h0 := checker_seg_empty P e χ (rookTo c ks) hχmem hseg
    rw [hinv.1] at h0
    exact absurd h0 (by simp)

theorem K3d_opp_seg_nonempty (P : Pos) (c : Color) (ks : Bool) (e : Sq) (hinv : CastleInv P c ks e)
    (hc0 : C0 P) (hgeom : ry e = c.home ∧ inSeg (kingTo c ks) e (rookTo c ks) = true) (hturn : P.turn = c.opp)
    (m : Move) (hm : m ∈ legalMoves P) (hnk : isKingMove P m = false) (hr : m.dst ≠ rookTo c ks) :
    ∃ z, inSeg (rookTo c ks) e z = true ∧ (play P m).board z ≠ none := by
  obtain ⟨q0, hq0, hqc0, -⟩ := legal_nonking_mem P m hm hnk
  rw [hturn] at hqc0
  have hsrcR : m.src ≠ rookTo c ks := fun hh => by
    have h1 : P.board (rookTo c ks) = some q0 := hh ▸ hq0
    have h2 := Option.some.inj (h1.symm.trans hinv.1)
    rw [h2] at hqc0
    exact opp_ne_self c hqc0
  have hevR : epVictim P m ≠ some (rookTo c ks) := by
    intro hv
    obtain ⟨-, -, hbv, -, -, -⟩ := epVictim_spec P m _ hm hv
    rw [hinv.1] at hbv
    simp only [Option.some.injEq, Piece.mk.injEq] at hbv
    exact absurd hbv.2 (by decide)
  have hbR' : (play P m).board (rookTo c ks) = some ⟨c, .rook⟩ := by
    rw [nonking_board_change P m hm hnk _ (Ne.symm hsrcR) (Ne.symm hr) hevR]
    exact hinv.1
  apply Classical.byContradiction
  intro hnn
  have hclr : ∀ z, inSeg (rookTo c ks) e z = true → (play P m).board z = none := by
    intro z hz
    by_cases hb : (play P m).board z = none
    · exact hb
    · exact absurd ⟨z, hz, hb⟩ hnn
  have hRe : rookTo c ks ≠ e := (inSeg_ne hgeom.2).2
  have hryeq : ry (rookTo c ks) = ry e := (k3_ry_rookTo c ks).trans hgeom.1.symm
  have horth : orthLine (rookTo c ks) e = true := by
    simp only [orthLine, aligned, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, Bool.or_eq_true]
    refine ⟨⟨hRe, Or.inl (Or.inr hryeq)⟩, Or.inr hryeq⟩
  have hatt : e ∈ attacks (play P m).board (rookTo c ks) ⟨c, .rook⟩ :=
    (mem_attacks_iff _ _ _ _).mpr ⟨horth, fun _ => hclr⟩
  have hke' : kingAt (play P m) c.opp e :=
    (kingAt_play_nonking P m hm hnk hc0.safe c.opp e).mpr hinv.2.2.1
  have hic : inCheck (play P m) c.opp = true := by
    rw [inCheck_iff]
    refine ⟨e, hke', ?_⟩
    rw [Color.opp_opp]
    exact (attacked_iff _ _ _).mpr ⟨_, _, hbR', rfl, hatt⟩
  rw [← hturn] at hic
  rw [legal_safe P m hm] at hic
  exact absurd hic (by decide)

theorem K3d_step_opp (P : Pos) (c : Color) (ks : Bool) (e : Sq) (hinv : CastleInv P c ks e) (hc0 : C0 P)
    (hgeom : ry e = c.home ∧ inSeg (kingTo c ks) e (rookTo c ks) = true) (hturn : P.turn = c.opp)
    (hchk : inCheck P P.turn = true) (m : Move) (hm : m ∈ legalMoves P) (hnk : isKingMove P m = false) :
    CastleInv (play P m) c ks e := by
  have hdstR := K3d_opp_rook_safe P c ks e hinv hc0 hgeom hturn hchk m hm hnk
  have hnon := K3d_opp_seg_nonempty P c ks e hinv hc0 hgeom hturn m hm hnk hdstR
  have hsd : m.src ≠ m.dst := legal_src_ne_dst P m hm
  obtain ⟨q0, hq0, hqc0, -⟩ := legal_nonking_mem P m hm hnk
  rw [hturn] at hqc0
  have hsrcR : m.src ≠ rookTo c ks := fun hh => by
    have h1 : P.board (rookTo c ks) = some q0 := hh ▸ hq0
    have h2 := Option.some.inj (h1.symm.trans hinv.1)
    have h3 : q0.color = c := by rw [h2]
    rw [hqc0] at h3
    exact opp_ne_self c h3.symm
  have hevR : epVictim P m ≠ some (rookTo c ks) := by
    intro hv
    obtain ⟨-, -, hbv, -, -, -⟩ := epVictim_spec P m _ hm hv
    rw [hinv.1] at hbv
    simp only [Option.some.injEq, Piece.mk.injEq] at hbv
    exact absurd hbv.2 (by decide)
  have hbR' : (play P m).board (rookTo c ks) = some ⟨c, .rook⟩ := by
    rw [nonking_board_change P m hm hnk _ (Ne.symm hsrcR) (Ne.symm hdstR) hevR]
    exact hinv.1
  have hkK' : kingAt (play P m) c (kingTo c ks) :=
    (kingAt_play_nonking P m hm hnk hc0.safe c _).mpr hinv.2.1
  have hke' : kingAt (play P m) c.opp e :=
    (kingAt_play_nonking P m hm hnk hc0.safe c.opp e).mpr hinv.2.2.1
  have hcols : ∀ z q, inSeg (rookTo c ks) e z = true → (play P m).board z = some q →
      q.color = c.opp := by
    intro z q hz hq
    by_cases hzd : z = m.dst
    · subst hzd
      rw [play_board_dst] at hq
      cases hp : m.promo with
      | none =>
        rw [hp] at hq
        dsimp only [] at hq
        rw [hq0] at hq
        have hq2 := Option.some.inj hq
        rw [← hq2]
        exact hqc0
      | some kk =>
        rw [hp] at hq
        dsimp only [] at hq
        rw [hq0] at hq
        rw [Option.map_some] at hq
        have hq2 := Option.some.inj hq
        rw [← hq2]
        exact hqc0
    · by_cases hzs : z = m.src
      · subst hzs
        rw [play_board_src P m hsd] at hq
        exact absurd hq (by simp)
      · have hzv : epVictim P m ≠ some z := by
          intro hv
          have hze : (play P m).board z = none := play_board_epVictim P m z hv hzd
          rw [hze] at hq
          exact absurd hq (by simp)
        rw [nonking_board_change P m hm hnk z hzs hzd hzv] at hq
        exact hinv.2.2.2.2 z q hz hq
  exact ⟨hbR', hkK', hke', hnon, hcols⟩

theorem K3e_contra (P : Pos) (c : Color) (ks : Bool) (e : Sq) (hinv : CastleInv P c ks e)
    (hgeom : ry e = c.home ∧ inSeg (kingTo c ks) e (rookTo c ks) = true)
    (hempty : ∀ z, inSeg (kingTo c ks) e z = true → P.board z = none) : False := by
  obtain ⟨hbR, -, -, -, -⟩ := hinv
  have h := hempty _ hgeom.2
  rw [hbR] at h
  exact absurd h (by simp)

theorem K3_t_ne_one (p : Pos) (ms : List Move) (hr : Reachable p) (hs : IsCheckSeq p ms)
    (h1 : 1 < ms.length) (hc : isCastle (posAt p ms 0) ms[0] = true) :
    isKingMove (posAt p ms 1) ms[1] = false := by
  obtain ⟨hm0, hg0, hpl1⟩ := checkSeq_step p ms hs 0 (by omega)
  obtain ⟨hm1, hg1, hpl2⟩ := checkSeq_step p ms hs 1 h1
  have hc0P0 : C0 (posAt p ms 0) := reachable_c0 _ (checkSeq_reachable p ms hr hs 0 (Nat.zero_le _))
  have hc0P1 : C0 (posAt p ms 1) := reachable_c0 _ (checkSeq_reachable p ms hr hs 1 (by omega))
  have hc0P2 : C0 (posAt p ms 2) := reachable_c0 _ (checkSeq_reachable p ms hr hs 2 (by omega))
  obtain ⟨e, he⟩ := king_square_exists _ hc0P0 (posAt p ms 0).turn.opp
  obtain ⟨hchk1, hattR⟩ := K3a_castle_checker _ _ e hc0P0 hm0 hc hg0 he
  rw [← hpl1] at hattR
  obtain ⟨hchg, hbK, hbR, hb4, hbc, hrookatt, hs4⟩ := castle_play_facts _ _ hm0 hc
  rw [← hpl1] at hchg hbK hbR hb4 hbc
  have ht1 : (posAt p ms 1).turn = (posAt p ms 0).turn.opp := by rw [hpl1]; exact play_turn _ _
  have hking0 : isKingMove (posAt p ms 0) ms[0] = true := by
    have h2 := hc
    unfold isCastle at h2
    exact (Bool.and_eq_true _ _ |>.mp h2).1
  have hksrc : (posAt p ms 0).board ms[0].src = some ⟨(posAt p ms 0).turn, .king⟩ :=
    kingMove_src _ _ hm0 hking0
  have hnes : e ≠ ms[0].src := by
    intro hh
    have he2 : (posAt p ms 0).board e = some ⟨(posAt p ms 0).turn.opp, .king⟩ := he
    rw [hh, hksrc] at he2
    have h2 := congrArg Piece.color (Option.some.inj he2)
    exact opp_ne_self (posAt p ms 0).turn h2
  have heP1 : kingAt (posAt p ms 1) (posAt p ms 0).turn.opp e := by
    have h := king_stay _ _ hm0 hc0P0.safe _ e he hnes
    rw [← hpl1] at h
    exact h
  have heP1b : kingAt (posAt p ms 1) (posAt p ms 1).turn e := by rw [ht1]; exact heP1
  cases hk1 : isKingMove (posAt p ms 1) ms[1] with
  | false => rfl
  | true =>
    exfalso
    have hc1 : isCastle (posAt p ms 1) ms[1] = false := K1_castle_first p ms hr hs 1 (Nat.le_refl 1) h1
    have heK1 : kingAt (posAt p ms 1) (posAt p ms 1).turn.opp
        (kingTo (posAt p ms 0).turn (castleSide ms[0])) := by
      rw [ht1, Color.opp_opp]
      exact hbK
    obtain ⟨S, q, hbSq1, hqcS, hslider, hsegS, hattS, hald⟩ :=
      lemmaD _ ms[1] _ hc0P1 hm1 hk1 hc1 hg1 heK1
    have hsrc1 : ms[1].src = e :=
      king_square_unique _ hc0P1 _ _ _ (kingMove_src _ _ hm1 hk1) heP1b
    rw [hsrc1] at hsegS
    rw [← hpl2] at hattS
    obtain ⟨hgeomS, hclearS⟩ := (mem_attacks_iff _ _ _ _).mp hattS
    have hcpS := hclearS hslider
    obtain ⟨hgeomR, hclearR⟩ := (mem_attacks_iff _ _ _ _).mp hattR
    have horth : orthLine (rookTo (posAt p ms 0).turn (castleSide ms[0])) e = true := hgeomR
    have hcpR : clearPath (posAt p ms 1).board (rookTo (posAt p ms 0).turn (castleSide ms[0])) e :=
      hclearR rfl
    have hnb : inSeg (rookTo (posAt p ms 0).turn (castleSide ms[0])) e
        (kingTo (posAt p ms 0).turn (castleSide ms[0])) = false := by
      cases hh : inSeg (rookTo (posAt p ms 0).turn (castleSide ms[0])) e
        (kingTo (posAt p ms 0).turn (castleSide ms[0])) with
      | false => rfl
      | true =>
        have hn := hcpR _ hh
        rw [hbK] at hn
        exact absurd hn (by simp)
    have hdKE : 2 ≤ kdist (kingTo (posAt p ms 0).turn (castleSide ms[0])) e := by
      cases htu : (posAt p ms 0).turn with
      | white =>
        rw [htu] at hbK heP1
        exact hc0P1.apart _ _ hbK heP1
      | black =>
        rw [htu] at hbK heP1
        have h3 := hc0P1.apart _ _ heP1 hbK
        rw [kdist_comm] at h3
        exact h3
    have hk4 : (posAt p ms 0).board (sq 4 (posAt p ms 0).turn.home) =
        some ⟨(posAt p ms 0).turn, .king⟩ := by
      have hsrc0 := (castle_shape _ _ hm0 hc).1
      rw [← hsrc0]
      exact hksrc
    have hd4E : 2 ≤ kdist (sq 4 (posAt p ms 0).turn.home) e := by
      cases htu : (posAt p ms 0).turn with
      | white =>
        rw [htu] at hk4 he
        exact hc0P0.apart _ _ hk4 he
      | black =>
        rw [htu] at hk4 he
        have h3 := hc0P0.apart _ _ he hk4
        rw [kdist_comm] at h3
        exact h3
    have hne4 : e ≠ sq 4 (posAt p ms 0).turn.home := by
      intro hh
      have he2 : (posAt p ms 0).board e = some ⟨(posAt p ms 0).turn.opp, .king⟩ := he
      rw [hh, hk4] at he2
      have h2 := congrArg Piece.color (Option.some.inj he2)
      exact opp_ne_self (posAt p ms 0).turn h2
    have halKE : aligned (kingTo (posAt p ms 0).turn (castleSide ms[0])) e = true := by
      have h3 := (inSeg_aligned S (kingTo (posAt p ms 0).turn (castleSide ms[0])) e hsegS).2.1
      rw [aligned_comm] at h3
      exact h3
    obtain ⟨hrye, hsegKR⟩ := K3b_castle_geom _ _ e halKE hdKE hd4E hne4 horth hnb
    have h1c : inSeg (kingTo (posAt p ms 0).turn (castleSide ms[0])) S e = true :=
      inSeg_comm S _ e ▸ hsegS
    have hsegSR : inSeg S (kingTo (posAt p ms 0).turn (castleSide ms[0]))
        (rookTo (posAt p ms 0).turn (castleSide ms[0])) = true :=
      inSeg_comm _ S _ ▸ inSeg_trans _ S e _ h1c hsegKR
    have hdstne : ms[1].dst ≠ rookTo (posAt p ms 0).turn (castleSide ms[0]) := by
      intro hh
      have halKR : aligned (kingTo (posAt p ms 0).turn (castleSide ms[0]))
          (rookTo (posAt p ms 0).turn (castleSide ms[0])) = true :=
        (inSeg_aligned _ e _ hsegKR).1
      rw [hh, aligned_comm, halKR] at hald
      exact absurd hald (by decide)
    have hRsrcc : e ≠ rookTo (posAt p ms 0).turn (castleSide ms[0]) := by
      intro hh
      have he2 : (posAt p ms 1).board e = some ⟨(posAt p ms 1).turn, .king⟩ := heP1b
      rw [hh, hbR] at he2
      have h2 := congrArg Piece.kind (Option.some.inj he2)
      exact Kind.noConfusion h2
    have hany : ((posAt p ms 0).board ms[0].src).any (fun q => q.kind == .pawn) = false := by
      rw [hksrc]
      rfl
    have hep0 : (posAt p ms 1).ep = none := by
      have h : (play (posAt p ms 0) ms[0]).ep = none := by
        rw [play_ep, hany, Bool.false_and]
        rfl
      rw [← hpl1] at h
      exact h
    have hepV : epVictim (posAt p ms 1) ms[1] ≠
        some (rookTo (posAt p ms 0).turn (castleSide ms[0])) := by
      intro hv
      obtain ⟨hepE, -⟩ := epVictim_spec _ _ _ hm1 hv
      rw [hep0] at hepE
      exact absurd hepE (by simp)
    have hbR2 : (posAt p ms 2).board (rookTo (posAt p ms 0).turn (castleSide ms[0])) =
        some ⟨(posAt p ms 0).turn, .rook⟩ := by
      have hRs1 : rookTo (posAt p ms 0).turn (castleSide ms[0]) ≠ ms[1].src := by
        rw [hsrc1]
        exact Ne.symm hRsrcc
      have h := play_board_other _ _ _ hRs1 (Ne.symm hdstne) hepV hc1
      rw [← hpl2] at h
      rw [h]
      exact hbR
    have hn := hcpS _ hsegSR
    rw [hbR2] at hn
    exact absurd hn (by simp)

theorem K3_inv_upto (p : Pos) (ms : List Move) (hr : Reachable p) (hs : IsCheckSeq p ms)
    (h0 : 0 < ms.length) (hc : isCastle (posAt p ms 0) ms[0] = true) (e : Sq) (he : kingAt p p.turn.opp e)
    (hgeom : ry e = p.turn.home ∧
      inSeg (kingTo p.turn (castleSide ms[0])) e (rookTo p.turn (castleSide ms[0])) = true)
    (k : Nat) (h2 : 2 ≤ k) (hk : k ≤ ms.length)
    (hnk : ∀ j (hj : j < ms.length), 1 ≤ j → j < k → isKingMove (posAt p ms j) ms[j] = false) :
    CastleInv (posAt p ms k) p.turn (castleSide ms[0]) e := by
  have h1l : 1 < ms.length := by omega
  obtain ⟨hm0, hg0, hpl1⟩ := checkSeq_step p ms hs 0 h0
  obtain ⟨hm1, -, hpl2⟩ := checkSeq_step p ms hs 1 h1l
  have hc0P0 : C0 (posAt p ms 0) := reachable_c0 _ (checkSeq_reachable p ms hr hs 0 (Nat.zero_le _))
  have hbase : CastleInv (posAt p ms 2) p.turn (castleSide ms[0]) e := by
    have hm1' : ms[1] ∈ legalMoves (play (posAt p ms 0) ms[0]) := by rw [← hpl1]; exact hm1
    have hnk1' : isKingMove (play (posAt p ms 0) ms[0]) ms[1] = false := by
      rw [← hpl1]
      exact hnk 1 h1l (Nat.le_refl 1) (by omega)
    have hb := K3c_reply _ ms[0] ms[1] e hc0P0 hm0 hc hg0 he hgeom hm1' hnk1'
    have hX : posAt p ms 2 = play (play (posAt p ms 0) ms[0]) ms[1] := by rw [hpl2, hpl1]
    rw [hX]
    exact hb
  have key : ∀ d, 2 + d ≤ k → CastleInv (posAt p ms (2 + d)) p.turn (castleSide ms[0]) e := by
    intro d hd
    induction d with
    | zero => exact hbase
    | succ d ih =>
      have hjl : 2 + d < ms.length := by omega
      have hinvd := ih (by omega)
      obtain ⟨hmj, hgj, hplj⟩ := checkSeq_step p ms hs (2 + d) hjl
      have hc0j : C0 (posAt p ms (2 + d)) :=
        reachable_c0 _ (checkSeq_reachable p ms hr hs _ (by omega))
      have hchkj : inCheck (posAt p ms (2 + d)) (posAt p ms (2 + d)).turn = true :=
        checkSeq_inCheck p ms hs (2 + d) (by omega) (by omega)
      have hnkj : isKingMove (posAt p ms (2 + d)) ms[2 + d] = false :=
        hnk _ hjl (by omega) (by omega)
      show CastleInv (posAt p ms (2 + d + 1)) _ _ _
      rw [hplj]
      by_cases hto : (posAt p ms (2 + d)).turn = p.turn
      · exact K3d_step_own _ _ _ _ hinvd hc0j hgeom hto hchkj _ hmj hnkj hgj
      · have hto2 : (posAt p ms (2 + d)).turn = p.turn.opp := color_eq_opp_of_ne _ _ hto
        exact K3d_step_opp _ _ _ _ hinvd hc0j hgeom hto2 hchkj _ hmj hnkj
  have hkk : k = 2 + (k - 2) := by omega
  rw [hkk]
  exact key (k - 2) (by omega)

theorem K3_castle_then_king (p : Pos) (ms : List Move) (hr : Reachable p) (hs : IsCheckSeq p ms)
    (h0 : 0 < ms.length) (hc : isCastle (posAt p ms 0) ms[0] = true) (t : Nat) (ht : 1 ≤ t) (htl : t < ms.length)
    (hkt : isKingMove (posAt p ms t) ms[t] = true)
    (hnk : ∀ k (hk : k < ms.length), 1 ≤ k → k < t → isKingMove (posAt p ms k) ms[k] = false) : False := by
  have h1l : 1 < ms.length := by omega
  have ht1 : isKingMove (posAt p ms 1) ms[1] = false := K3_t_ne_one p ms hr hs h1l hc
  have ht2 : 2 ≤ t := by
    rcases Nat.lt_or_ge t 2 with hlt2 | hge
    · have hteq : t = 1 := by omega
      exfalso
      subst hteq
      rw [ht1] at hkt
      exact absurd hkt (by decide)
    · exact hge
  obtain ⟨hm0, hg0, hpl1⟩ := checkSeq_step p ms hs 0 h0
  obtain ⟨hmt, hgt, -⟩ := checkSeq_step p ms hs t htl
  have hc0P0 : C0 (posAt p ms 0) := reachable_c0 _ (checkSeq_reachable p ms hr hs 0 (Nat.zero_le _))
  have hc0t : C0 (posAt p ms t) := reachable_c0 _ (checkSeq_reachable p ms hr hs t (Nat.le_of_lt htl))
  have hct : isCastle (posAt p ms t) ms[t] = false := K1_castle_first p ms hr hs t ht htl
  obtain ⟨e, he⟩ := king_square_exists _ hc0P0 (posAt p ms 0).turn.opp
  obtain ⟨-, hattR⟩ := K3a_castle_checker _ _ e hc0P0 hm0 hc hg0 he
  rw [← hpl1] at hattR
  obtain ⟨-, hbK, hbR, -, -, -, -⟩ := castle_play_facts _ _ hm0 hc
  rw [← hpl1] at hbK hbR
  have hking0 : isKingMove (posAt p ms 0) ms[0] = true := by
    have h2 := hc
    unfold isCastle at h2
    exact (Bool.and_eq_true _ _ |>.mp h2).1
  have hksrc : (posAt p ms 0).board ms[0].src = some ⟨(posAt p ms 0).turn, .king⟩ :=
    kingMove_src _ _ hm0 hking0
  have hnes : e ≠ ms[0].src := by
    intro hh
    have he2 : (posAt p ms 0).board e = some ⟨(posAt p ms 0).turn.opp, .king⟩ := he
    rw [hh, hksrc] at he2
    have h2 := congrArg Piece.color (Option.some.inj he2)
    exact opp_ne_self (posAt p ms 0).turn h2
  have heP1 : kingAt (posAt p ms 1) (posAt p ms 0).turn.opp e := by
    have h := king_stay _ _ hm0 hc0P0.safe _ e he hnes
    rw [← hpl1] at h
    exact h
  have hkf : ∀ (c : Color) (s : Sq), kingAt (posAt p ms t) c s ↔ kingAt (posAt p ms 1) c s :=
    fun c s => kings_fixed p ms hr hs 1 t ht (Nat.le_of_lt htl) (fun k hk2 h1k hkt2 => hnk k hk2 h1k hkt2) c s
  have hew : kingAt (posAt p ms t) p.turn (kingTo p.turn (castleSide ms[0])) := (hkf _ _).mpr hbK
  have heb : kingAt (posAt p ms t) p.turn.opp e := (hkf _ _).mpr heP1
  have hd : 2 ≤ kdist (kingTo p.turn (castleSide ms[0])) e := by
    cases htu : p.turn with
    | white =>
      rw [htu] at hew heb
      exact hc0t.apart _ _ hew heb
    | black =>
      rw [htu] at hew heb
      have h3 := hc0t.apart _ _ heb hew
      rw [kdist_comm] at h3
      exact h3
  have hk4 : (posAt p ms 0).board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ := by
    have hsrc0 := (castle_shape _ _ hm0 hc).1
    have h2 : (posAt p ms 0).board (sq 4 (posAt p ms 0).turn.home) =
        some ⟨(posAt p ms 0).turn, .king⟩ := by
      rw [← hsrc0]
      exact hksrc
    exact h2
  have he0 : (posAt p ms 0).board e = some ⟨p.turn.opp, .king⟩ := he
  have hd0 : 2 ≤ kdist (sq 4 p.turn.home) e := by
    cases htu : p.turn with
    | white =>
      rw [htu] at hk4 he0
      exact hc0P0.apart _ _ hk4 he0
    | black =>
      rw [htu] at hk4 he0
      have h3 := hc0P0.apart _ _ he0 hk4
      rw [kdist_comm] at h3
      exact h3
  have hne4 : e ≠ sq 4 p.turn.home := by
    intro hh
    rw [hh, hk4] at he0
    have h2 := congrArg Piece.color (Option.some.inj he0)
    exact opp_ne_self p.turn h2
  obtain ⟨hgeomR, hclearR⟩ := (mem_attacks_iff _ _ _ _).mp hattR
  have horth : orthLine (rookTo p.turn (castleSide ms[0])) e = true := hgeomR
  have hcpR : clearPath (posAt p ms 1).board (rookTo p.turn (castleSide ms[0])) e := hclearR rfl
  have hbK' : (posAt p ms 1).board (kingTo p.turn (castleSide ms[0])) = some ⟨p.turn, .king⟩ := hbK
  have hnb : inSeg (rookTo p.turn (castleSide ms[0])) e (kingTo p.turn (castleSide ms[0])) = false := by
    cases hh : inSeg (rookTo p.turn (castleSide ms[0])) e (kingTo p.turn (castleSide ms[0])) with
    | false => rfl
    | true =>
      have hn := hcpR _ hh
      rw [hbK'] at hn
      exact absurd hn (by simp)
  have hgeomK := K3b_castle_geom p.turn (castleSide ms[0]) e
  by_cases hto : (posAt p ms t).turn = p.turn
  · have hsrc_t : ms[t].src = kingTo p.turn (castleSide ms[0]) := by
      have h1 := kingMove_src _ _ hmt hkt
      have hew2 : kingAt (posAt p ms t) (posAt p ms t).turn
          (kingTo (posAt p ms t).turn (castleSide ms[0])) := by
        rw [hto]
        exact hew
      have h3 := king_square_unique _ hc0t _ _ _ h1 hew2
      rw [hto] at h3
      exact h3
    have he_t : kingAt (posAt p ms t) (posAt p ms t).turn.opp e := by rw [hto]; exact heb
    have hal := lemmaD_aligned _ ms[t] e hc0t hmt hkt hct hgt he_t
    rw [hsrc_t] at hal
    have hgeom2 := hgeomK hal hd hd0 hne4 horth hnb
    have hinv : CastleInv (posAt p ms t) p.turn (castleSide ms[0]) e :=
      K3_inv_upto p ms hr hs h0 hc e he hgeom2 t ht2 (Nat.le_of_lt htl) hnk
    have hempty : ∀ z, inSeg (kingTo p.turn (castleSide ms[0])) e z = true →
        (posAt p ms t).board z = none := by
      have h2 := lemmaD_seg_empty _ ms[t] e hc0t hmt hkt hct hgt he_t
      rw [hsrc_t] at h2
      exact h2
    exact K3e_contra _ _ _ _ hinv hgeom2 hempty
  · have hto2 : (posAt p ms t).turn = p.turn.opp := color_eq_opp_of_ne _ _ hto
    have hsrc_t : ms[t].src = e := by
      have h1 := kingMove_src _ _ hmt hkt
      have h2 : kingAt (posAt p ms t) (posAt p ms t).turn e := by rw [hto2]; exact heb
      exact king_square_unique _ hc0t _ _ _ h1 h2
    have heK_t : kingAt (posAt p ms t) (posAt p ms t).turn.opp (kingTo p.turn (castleSide ms[0])) := by
      rw [hto2, Color.opp_opp]
      exact hew
    have hal := lemmaD_aligned _ ms[t] (kingTo p.turn (castleSide ms[0])) hc0t hmt hkt hct hgt heK_t
    rw [hsrc_t, aligned_comm] at hal
    have hgeom2 := hgeomK hal hd hd0 hne4 horth hnb
    have hinv : CastleInv (posAt p ms t) p.turn (castleSide ms[0]) e :=
      K3_inv_upto p ms hr hs h0 hc e he hgeom2 t ht2 (Nat.le_of_lt htl) hnk
    have hempty : ∀ z, inSeg (kingTo p.turn (castleSide ms[0])) e z = true →
        (posAt p ms t).board z = none := by
      have h2 := lemmaD_seg_empty _ ms[t] (kingTo p.turn (castleSide ms[0])) hc0t hmt hkt hct hgt heK_t
      rw [hsrc_t] at h2
      intro z hz
      exact h2 z (inSeg_comm _ e z ▸ hz)
    exact K3e_contra _ _ _ _ hinv hgeom2 hempty

theorem kingPlies_first (p : Pos) (ms : List Move) (h : 1 ≤ kingPlies p ms) :
    ∃ i, ∃ (hi : i < ms.length), isKingMove (posAt p ms i) ms[i] = true ∧
      ∀ k (hk : k < ms.length), k < i → isKingMove (posAt p ms k) ms[k] = false := by
  induction ms generalizing p with
  | nil => exact absurd h (by simp [kingPlies])
  | cons m ms ih =>
    cases hk : isKingMove p m with
    | true =>
      exact ⟨0, Nat.succ_pos _, hk, fun k hk1 hk2 => absurd hk2 (by omega)⟩
    | false =>
      have h' : 1 ≤ kingPlies (play p m) ms := by
        have e : kingPlies p (m :: ms) = kingPlies (play p m) ms := by simp [kingPlies, hk]
        omega
      obtain ⟨i, hi, hki, hmin⟩ := ih (play p m) h'
      refine ⟨i + 1, ?_, hki, ?_⟩
      · show i + 1 < ms.length + 1
        omega
      · intro k hkk hlt
        cases k with
        | zero => exact hk
        | succ k =>
          have hk' : k < ms.length := by
            have : k + 1 < ms.length + 1 := hkk
            omega
          exact hmin k hk' (by omega)

theorem kingPlies_two (p : Pos) (ms : List Move) (h : 2 ≤ kingPlies p ms) :
    ∃ i j, ∃ (hi : i < ms.length) (hj : j < ms.length), i < j ∧
      isKingMove (posAt p ms i) ms[i] = true ∧ isKingMove (posAt p ms j) ms[j] = true ∧
      ∀ k (hk : k < ms.length), i < k → k < j → isKingMove (posAt p ms k) ms[k] = false := by
  induction ms generalizing p with
  | nil => exact absurd h (by simp [kingPlies])
  | cons m ms ih =>
    cases hk : isKingMove p m with
    | true =>
      have h' : 1 ≤ kingPlies (play p m) ms := by
        have e : kingPlies p (m :: ms) = 1 + kingPlies (play p m) ms := by simp [kingPlies, hk]
        omega
      obtain ⟨j, hj, hkj, hmin⟩ := kingPlies_first (play p m) ms h'
      refine ⟨0, j + 1, Nat.succ_pos _, ?_, Nat.zero_lt_succ _, hk, hkj, ?_⟩
      · show j + 1 < ms.length + 1
        omega
      · intro k hkk h0 hlt
        cases k with
        | zero => omega
        | succ k =>
          have hk' : k < ms.length := by
            have : k + 1 < ms.length + 1 := hkk
            omega
          exact hmin k hk' (by omega)
    | false =>
      have h' : 2 ≤ kingPlies (play p m) ms := by
        have e : kingPlies p (m :: ms) = kingPlies (play p m) ms := by simp [kingPlies, hk]
        omega
      obtain ⟨i, j, hi, hj, hij, hki, hkj, hmid⟩ := ih (play p m) h'
      refine ⟨i + 1, j + 1, ?_, ?_, ?_, hki, hkj, ?_⟩
      · show i + 1 < ms.length + 1
        omega
      · show j + 1 < ms.length + 1
        omega
      · omega
      · intro k hkk hgt hlt
        cases k with
        | zero => omega
        | succ k =>
          have hk' : k < ms.length := by
            have : k + 1 < ms.length + 1 := hkk
            omega
          exact hmid k hk' (by omega) (by omega)

theorem posAt_drop (p : Pos) (ms : List Move) (i k : Nat) :
    posAt (posAt p ms i) (ms.drop i) k = posAt p ms (i + k) := by
  simp only [posAt, after, List.take_add, List.foldl_append]

theorem checkSeq_drop (p : Pos) (ms : List Move) (hs : IsCheckSeq p ms) (i : Nat) :
    IsCheckSeq (posAt p ms i) (ms.drop i) := by
  induction ms generalizing p i with
  | nil => simp [IsCheckSeq]
  | cons m ms ih =>
    obtain ⟨hm, hg, hs'⟩ : m ∈ legalMoves p ∧ givesCheck p m = true ∧ IsCheckSeq (play p m) ms := hs
    cases i with
    | zero => exact ⟨hm, hg, hs'⟩
    | succ i => exact ih (play p m) hs' i

theorem theoremK' (p : Pos) (ms : List Move) (hr : Reachable p) (hs : IsCheckSeq p ms) : kingPlies p ms ≤ 1 := by
  by_cases h2 : 2 ≤ kingPlies p ms
  · obtain ⟨i, j, hi, hj, hij, hki, hkj, hmid⟩ := kingPlies_two p ms h2
    cases hci : isCastle (posAt p ms i) ms[i] with
    | false => exact (K2_two_plain p ms hr hs i j hij hj hki hci hkj hmid).elim
    | true =>
      obtain ⟨n, hn⟩ : ∃ n, j = i + n := ⟨j - i, by omega⟩
      subst hn
      have hrc : Reachable (posAt p ms i) := checkSeq_reachable p ms hr hs i (Nat.le_of_lt hi)
      have hcs : IsCheckSeq (posAt p ms i) (ms.drop i) := checkSeq_drop p ms hs i
      have hlen : (ms.drop i).length = ms.length - i := List.length_drop
      have hjl : n < (ms.drop i).length := by rw [hlen]; omega
      have h0n : 0 < (ms.drop i).length := by rw [hlen]; omega
      have hc' : isCastle (posAt (posAt p ms i) (ms.drop i) 0) (ms.drop i)[0] = true := by
        rw [List.getElem_drop]
        exact hci
      have hkj' : isKingMove (posAt (posAt p ms i) (ms.drop i) n) (ms.drop i)[n] = true := by
        rw [posAt_drop, List.getElem_drop]
        exact hkj
      have hnk' : ∀ k (hk : k < (ms.drop i).length), 1 ≤ k → k < n →
          isKingMove (posAt (posAt p ms i) (ms.drop i) k) (ms.drop i)[k] = false := by
        intro k hkl h1k hkjt
        rw [hlen] at hkl
        rw [posAt_drop, List.getElem_drop]
        exact hmid (i + k) (by omega) (by omega) (by omega)
      exact (K3_castle_then_king _ _ hrc hcs h0n hc' n (by omega) hjl hkj' hnk').elim
  · omega

end Chess.C364
