import ChessProof.C364.Moves

namespace Chess.C364

open Chess

theorem sq_val (f r : Nat) (hf : f < 8) (hr : r < 8) : (sq f r).val = r * 8 + f :=
  Nat.mod_eq_of_lt (by omega)

theorem sq_file (f r : Nat) (hf : f < 8) (hr : r < 8) : (sq f r).file = f := by
  show ((r * 8 + f) % 64) % 8 = f
  have hv : (r * 8 + f) % 64 = r * 8 + f := Nat.mod_eq_of_lt (by omega)
  rw [hv]; omega

theorem sq_rank (f r : Nat) (hf : f < 8) (hr : r < 8) : (sq f r).rank = r := by
  show ((r * 8 + f) % 64) / 8 = r
  have hv : (r * 8 + f) % 64 = r * 8 + f := Nat.mod_eq_of_lt (by omega)
  rw [hv]; omega

theorem fx_sq (f r : Nat) (hf : f < 8) (hr : r < 8) : fx (sq f r) = (f : Int) := by
  show ((sq f r).file : Int) = (f : Int)
  rw [sq_file f r hf hr]

theorem ry_sq (f r : Nat) (hf : f < 8) (hr : r < 8) : ry (sq f r) = (r : Int) := by
  show ((sq f r).rank : Int) = (r : Int)
  rw [sq_rank f r hf hr]

theorem initial_wk (s : Sq) : initial.board s = some ⟨.white, .king⟩ ↔ s = sq 4 0 := by
  decide +revert +kernel

theorem initial_bk (s : Sq) : initial.board s = some ⟨.black, .king⟩ ↔ s = sq 4 7 := by
  decide +revert +kernel

theorem initial_pawn_w (s : Sq) : initial.board s = some ⟨.white, .pawn⟩ → ry s ≠ 0 ∧ ry s ≠ 7 := by
  decide +revert +kernel

theorem initial_pawn_b (s : Sq) : initial.board s = some ⟨.black, .pawn⟩ → ry s ≠ 0 ∧ ry s ≠ 7 := by
  decide +revert +kernel

theorem initial_apart (w b : Sq) (hw : initial.board w = some ⟨.white, .king⟩)
    (hb : initial.board b = some ⟨.black, .king⟩) : 2 ≤ kdist w b := by
  obtain rfl := (initial_wk w).mp hw
  obtain rfl := (initial_bk b).mp hb
  decide

theorem initial_safe : inCheck initial initial.turn.opp = false := by
  decide +revert +kernel

theorem initial_ep (t : Sq) (h : initial.ep = some t) : epOk initial t :=
  absurd h (by decide +revert)

theorem initial_c0 : C0 initial :=
  ⟨⟨sq 4 0, fun s => initial_wk s⟩, ⟨sq 4 7, fun s => initial_bk s⟩, initial_apart,
    fun s c h => by cases c with
      | white => exact initial_pawn_w s h
      | black => exact initial_pawn_b s h,
    initial_safe, initial_ep⟩

theorem castleMove_full (p : Pos) (m : Move) (h : m ∈ castleMoves p) :
    (m = ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ ∧
        p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ ∧
        p.board (sq 7 p.turn.home) = some ⟨p.turn, .rook⟩ ∧
        p.board (sq 5 p.turn.home) = none ∧ p.board (sq 6 p.turn.home) = none) ∨
      (m = ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ ∧
        p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ ∧
        p.board (sq 0 p.turn.home) = some ⟨p.turn, .rook⟩ ∧
        p.board (sq 3 p.turn.home) = none ∧ p.board (sq 2 p.turn.home) = none) := by
  unfold castleMoves at h
  dsimp only at h
  by_cases hout : ((p.board (sq 4 p.turn.home) == some ⟨p.turn, .king⟩) &&
      !attacked p.board (sq 4 p.turn.home) p.turn.opp) = true
  · obtain ⟨hke, -⟩ := Bool.and_eq_true _ _ |>.mp hout
    have hk4 : p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ := beq_iff_eq.mp hke
    rw [if_pos hout, List.mem_append] at h
    rcases h with h | h
    · by_cases hK : ((p.castleK p.turn && p.board (sq 7 p.turn.home) == some ⟨p.turn, .rook⟩ &&
          [5, 6].all fun f => empty p.board (sq f p.turn.home)) &&
          !attacked p.board (sq 5 p.turn.home) p.turn.opp) = true
      · rw [if_pos hK, List.mem_singleton] at h
        obtain rfl := h
        obtain ⟨hf, -⟩ := Bool.and_eq_true _ _ |>.mp hK
        obtain ⟨hkr, hem⟩ := Bool.and_eq_true _ _ |>.mp hf
        obtain ⟨-, hr7⟩ := Bool.and_eq_true _ _ |>.mp hkr
        rw [List.all_eq_true] at hem
        have h5 := hem 5 (by simp)
        have h6 := hem 6 (by simp)
        exact Or.inl ⟨rfl, hk4, beq_iff_eq.mp hr7, empty_eq_none _ _ h5, empty_eq_none _ _ h6⟩
      · rw [if_neg hK] at h
        exact absurd h (not_mem_nil' m)
    · by_cases hQ : ((p.castleQ p.turn && p.board (sq 0 p.turn.home) == some ⟨p.turn, .rook⟩ &&
          [1, 2, 3].all fun f => empty p.board (sq f p.turn.home)) &&
          !attacked p.board (sq 3 p.turn.home) p.turn.opp) = true
      · rw [if_pos hQ, List.mem_singleton] at h
        obtain rfl := h
        obtain ⟨hf, -⟩ := Bool.and_eq_true _ _ |>.mp hQ
        obtain ⟨hkr, hem⟩ := Bool.and_eq_true _ _ |>.mp hf
        obtain ⟨-, hr0⟩ := Bool.and_eq_true _ _ |>.mp hkr
        rw [List.all_eq_true] at hem
        have h3 := hem 3 (by simp)
        have h2 := hem 2 (by simp)
        exact Or.inr ⟨rfl, hk4, beq_iff_eq.mp hr0, empty_eq_none _ _ h3, empty_eq_none _ _ h2⟩
      · rw [if_neg hQ] at h
        exact absurd h (not_mem_nil' m)
  · rw [if_neg hout] at h
    exact absurd h (not_mem_nil' m)

theorem legal_promo_kind (p : Pos) (m : Move) (hm : m ∈ legalMoves p) (k : Kind)
    (hp : m.promo = some k) : k = .knight ∨ k = .bishop ∨ k = .rook ∨ k = .queen := by
  have hps := legal_mem_pseudo p m hm
  unfold pseudo at hps
  rw [List.mem_append] at hps
  rcases hps with hps | hps
  · rw [List.mem_flatMap] at hps
    obtain ⟨s, -, hms⟩ := hps
    cases hb : p.board s with
    | none =>
      rw [hb] at hms
      exact absurd hms (not_mem_nil' m)
    | some q =>
      rw [hb] at hms
      dsimp only at hms
      by_cases hcq : (q.color == p.turn) = true
      · rw [if_pos hcq] at hms
        obtain ⟨qc, qk⟩ := q
        cases qk with
        | pawn =>
          change m ∈ pawnMoves p s qc at hms
          unfold pawnMoves at hms
          dsimp only at hms
          simp only [List.mem_append, List.mem_flatMap, List.mem_map, Option.mem_toList] at hms
          rcases hms with ⟨t, -, hm'⟩ | ⟨t, -, hm'⟩
          · by_cases hL : (t.rank == qc.last) = true
            · rw [if_pos hL, List.mem_map] at hm'
              obtain ⟨k0, hk0, hm''⟩ := hm'
              have hkk : k0 = k := by
                have h1 : (⟨s, t, some k0⟩ : Move) = m := hm''
                rw [← h1] at hp
                exact Option.some.inj hp
              subst hkk
              simpa using hk0
            · rw [if_neg hL, List.mem_singleton] at hm'
              rw [hm'] at hp
              cases hp
          · rw [← hm'] at hp
            cases hp
        | knight =>
          simp only [pieceMoves, List.mem_map] at hms
          obtain ⟨t, -, hm'⟩ := hms
          rw [← hm'] at hp
          cases hp
        | bishop =>
          simp only [pieceMoves, List.mem_map] at hms
          obtain ⟨t, -, hm'⟩ := hms
          rw [← hm'] at hp
          cases hp
        | rook =>
          simp only [pieceMoves, List.mem_map] at hms
          obtain ⟨t, -, hm'⟩ := hms
          rw [← hm'] at hp
          cases hp
        | queen =>
          simp only [pieceMoves, List.mem_map] at hms
          obtain ⟨t, -, hm'⟩ := hms
          rw [← hm'] at hp
          cases hp
        | king =>
          simp only [pieceMoves, List.mem_map] at hms
          obtain ⟨t, -, hm'⟩ := hms
          rw [← hm'] at hp
          cases hp
      · rw [if_neg hcq] at hms
        exact absurd hms (not_mem_nil' m)
  · obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ := castleMove_full p m hps <;> cases hp

theorem play_board_castleK (p : Pos) (hk : p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩) (z : Sq) :
    (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board z =
      if z == sq 6 p.turn.home then p.board (sq 4 p.turn.home)
      else if z == sq 4 p.turn.home then none
      else if z == sq 5 p.turn.home then p.board (sq 7 p.turn.home)
      else if z == sq 7 p.turn.home then none
      else p.board z := by
  have e3 : (sq 4 p.turn.home).file = 4 := sq_file 4 _ (by decide) (home_lt _)
  have e4 : (sq 6 p.turn.home).file = 6 := sq_file 6 _ (by decide) (home_lt _)
  have e5 : (sq 4 p.turn.home).rank = p.turn.home := sq_rank 4 _ (by decide) (home_lt _)
  have e8 : (Kind.king == Kind.pawn) = false := rfl
  have e9 : ((none : Option Sq) == some z) = false := rfl
  unfold play
  dsimp only
  rw [hk, e3, e4, e5]
  simp only [Option.any_some, beq_self_eq_true, Bool.and_true, if_true, if_false,
    reduceCtorEq, ite_true, ite_false, Bool.false_and, Bool.and_false, Bool.or_false, e8, e9]

theorem play_board_castleQ (p : Pos) (hk : p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩) (z : Sq) :
    (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board z =
      if z == sq 2 p.turn.home then p.board (sq 4 p.turn.home)
      else if z == sq 4 p.turn.home then none
      else if z == sq 3 p.turn.home then p.board (sq 0 p.turn.home)
      else if z == sq 0 p.turn.home then none
      else p.board z := by
  have e3 : (sq 4 p.turn.home).file = 4 := sq_file 4 _ (by decide) (home_lt _)
  have e4 : (sq 2 p.turn.home).file = 2 := sq_file 2 _ (by decide) (home_lt _)
  have e5 : (sq 4 p.turn.home).rank = p.turn.home := sq_rank 4 _ (by decide) (home_lt _)
  have e6 : ((4 : Nat) + 2 == 2) = false := rfl
  have e7 : ((2 : Nat) + 2 == 4) = true := rfl
  have e8 : (Kind.king == Kind.pawn) = false := rfl
  have e9 : ((none : Option Sq) == some z) = false := rfl
  unfold play
  dsimp only
  rw [hk, e3, e4, e5]
  simp only [Option.any_some, beq_self_eq_true, Bool.and_true, if_true, if_false,
    reduceCtorEq, ite_true, ite_false, Bool.false_and, Bool.and_false, Bool.or_false, e6, e7, e8, e9]

theorem king_back (p : Pos) (m : Move) (hm : m ∈ legalMoves p)
    (c : Color) (s : Sq) (h : (play p m).board s = some ⟨c, .king⟩) :
    (p.board s = some ⟨c, .king⟩ ∧ s ≠ m.src ∧ s ≠ m.dst) ∨
      (s = m.dst ∧ p.board m.src = some ⟨c, .king⟩ ∧ m.promo = none) := by
  have hsd : m.src ≠ m.dst := legal_src_ne_dst p m hm
  by_cases hdst : s = m.dst
  · subst hdst
    right
    have hpr : m.promo = none := by
      cases hpr : m.promo with
      | none => rfl
      | some k =>
        exfalso
        have hk0 := legal_promo_kind p m hm k hpr
        rw [play_board_dst, hpr] at h
        cases hbs : p.board m.src with
        | none => simp [hbs] at h
        | some q =>
          rw [hbs] at h
          simp only [Option.map_some, Option.some.injEq, Piece.mk.injEq] at h
          rcases hk0 with rfl | rfl | rfl | rfl <;> exact absurd h.2 (by decide)
    have hbs' : p.board m.src = some ⟨c, .king⟩ := by
      rw [play_board_dst, hpr] at h
      exact h
    exact ⟨rfl, hbs', hpr⟩
  · by_cases hsrc : s = m.src
    · subst hsrc
      rw [play_board_src p m hsd] at h
      simp at h
    · cases hv : epVictim p m with
      | some v =>
        by_cases hsv : s = v
        · subst hsv
          rw [play_board_epVictim p m _ hv hdst] at h
          simp at h
        · have he : epVictim p m ≠ some s := by
            rw [hv]
            intro hh
            exact hsv (Option.some.inj hh).symm
          have hcond : ((p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file &&
              empty p.board m.dst) = true := by
            unfold epVictim at hv
            split at hv
            · assumption
            · contradiction
          obtain ⟨hpf, -⟩ := Bool.and_eq_true _ _ |>.mp hcond
          obtain ⟨hpn, -⟩ := Bool.and_eq_true _ _ |>.mp hpf
          have hki : isKingMove p m = false := by
            cases hbs : p.board m.src with
            | none =>
              unfold isKingMove
              rw [hbs]
              rfl
            | some q =>
              have hqn : q.kind = .pawn := by
                rw [hbs] at hpn
                have h2 : (q.kind == .pawn) = true := by simpa using hpn
                exact beq_iff_eq.mp h2
              unfold isKingMove
              rw [hbs]
              simp only [Option.any_some]
              rw [hqn]
              rfl
          have hcast : isCastle p m = false := by
            unfold isCastle
            rw [hki]
            rfl
          rw [play_board_other p m s hsrc hdst he hcast] at h
          exact Or.inl ⟨h, hsrc, hdst⟩
      | none =>
        by_cases hcast : isCastle p m = true
        · rcases castleMove_full p m (legal_castle_mem p m hm hcast) with
            ⟨rfl, hsrc4, hr7, h5, h6⟩ | ⟨rfl, hsrc4, hr0, h3, h2⟩
          · have hdst' : s ≠ sq 6 p.turn.home := hdst
            have hsrc' : s ≠ sq 4 p.turn.home := hsrc
            by_cases hs5 : s = sq 5 p.turn.home
            · subst hs5
              rw [play_board_castleK p hsrc4 _] at h
              rw [beq_eq_false_iff_ne.mpr (sq_ne_of_file 5 6 (by decide) (by decide) _ (home_lt _) (by decide)),
                beq_eq_false_iff_ne.mpr (sq_ne_of_file 5 4 (by decide) (by decide) _ (home_lt _) (by decide)),
                beq_self_eq_true] at h
              rw [hr7] at h
              simp only [Bool.false_eq_true, if_false, ite_true, Option.some.injEq, Piece.mk.injEq] at h
              exact absurd h.2 (by decide)
            · by_cases hs7 : s = sq 7 p.turn.home
              · subst hs7
                rw [play_board_castleK p hsrc4 _] at h
                rw [beq_eq_false_iff_ne.mpr (sq_ne_of_file 7 6 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_eq_false_iff_ne.mpr (sq_ne_of_file 7 4 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_eq_false_iff_ne.mpr (sq_ne_of_file 7 5 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_self_eq_true] at h
                simp at h
              · rw [play_board_castleK p hsrc4 s, beq_eq_false_iff_ne.mpr hdst',
                  beq_eq_false_iff_ne.mpr hsrc', beq_eq_false_iff_ne.mpr hs5,
                  beq_eq_false_iff_ne.mpr hs7] at h
                exact Or.inl ⟨h, hsrc, hdst⟩
          · have hdst' : s ≠ sq 2 p.turn.home := hdst
            have hsrc' : s ≠ sq 4 p.turn.home := hsrc
            by_cases hs3 : s = sq 3 p.turn.home
            · subst hs3
              rw [play_board_castleQ p hsrc4 _] at h
              rw [beq_eq_false_iff_ne.mpr (sq_ne_of_file 3 2 (by decide) (by decide) _ (home_lt _) (by decide)),
                beq_eq_false_iff_ne.mpr (sq_ne_of_file 3 4 (by decide) (by decide) _ (home_lt _) (by decide)),
                beq_self_eq_true] at h
              rw [hr0] at h
              simp only [Bool.false_eq_true, if_false, ite_true, Option.some.injEq, Piece.mk.injEq] at h
              exact absurd h.2 (by decide)
            · by_cases hs0 : s = sq 0 p.turn.home
              · subst hs0
                rw [play_board_castleQ p hsrc4 _] at h
                rw [beq_eq_false_iff_ne.mpr (sq_ne_of_file 0 2 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_eq_false_iff_ne.mpr (sq_ne_of_file 0 4 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_eq_false_iff_ne.mpr (sq_ne_of_file 0 3 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_self_eq_true] at h
                simp at h
              · rw [play_board_castleQ p hsrc4 s, beq_eq_false_iff_ne.mpr hdst',
                  beq_eq_false_iff_ne.mpr hsrc', beq_eq_false_iff_ne.mpr hs3,
                  beq_eq_false_iff_ne.mpr hs0] at h
                exact Or.inl ⟨h, hsrc, hdst⟩
        · have he : epVictim p m ≠ some s := by
            rw [hv]
            simp
          have hcast' : isCastle p m = false := Bool.not_eq_true _ |>.mp hcast
          rw [play_board_other p m s hsrc hdst he hcast'] at h
          exact Or.inl ⟨h, hsrc, hdst⟩

theorem kingMove_src (p : Pos) (m : Move) (hm : m ∈ legalMoves p) (hk : isKingMove p m = true) :
    p.board m.src = some ⟨p.turn, .king⟩ := by
  unfold isKingMove at hk
  obtain ⟨q2, hq2, hqcol⟩ := legal_src p m hm
  rw [hq2] at hk
  have hqk : q2.kind = .king := by
    have h2 : (q2.kind == .king) = true := by simpa using hk
    exact beq_iff_eq.mp h2
  obtain ⟨qc, qk⟩ := q2
  have hqcol' : qc = p.turn := hqcol
  cases qk with
  | king => rw [← hqcol']; exact hq2
  | pawn => exact Kind.noConfusion (show Kind.pawn = Kind.king from hqk)
  | knight => exact Kind.noConfusion (show Kind.knight = Kind.king from hqk)
  | bishop => exact Kind.noConfusion (show Kind.bishop = Kind.king from hqk)
  | rook => exact Kind.noConfusion (show Kind.rook = Kind.king from hqk)
  | queen => exact Kind.noConfusion (show Kind.queen = Kind.king from hqk)

theorem castleMove_isCastle (p : Pos) (m : Move) (h : m ∈ castleMoves p) : isCastle p m = true := by
  rcases castleMove_full p m h with ⟨rfl, hsrc4, -⟩ | ⟨rfl, hsrc4, -⟩
  · unfold isCastle isKingMove
    rw [hsrc4]
    simp [Option.any_some, sq_file 4 _ (by decide) (home_lt _), sq_file 6 _ (by decide) (home_lt _)]
  · unfold isCastle isKingMove
    rw [hsrc4]
    simp [Option.any_some, sq_file 4 _ (by decide) (home_lt _), sq_file 2 _ (by decide) (home_lt _)]

theorem kingMove_promo (p : Pos) (m : Move) (hm : m ∈ legalMoves p) (hk : isKingMove p m = true) :
    m.promo = none := by
  by_cases hcast : isCastle p m = true
  · rcases castleMove_full p m (legal_castle_mem p m hm hcast) with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  · have hps := legal_mem_pseudo p m hm
    unfold pseudo at hps
    rw [List.mem_append] at hps
    rcases hps with hps | hps
    · rw [List.mem_flatMap] at hps
      obtain ⟨s, -, hms⟩ := hps
      cases hb : p.board s with
      | none =>
        rw [hb] at hms
        exact absurd hms (not_mem_nil' m)
      | some q =>
        rw [hb] at hms
        dsimp only at hms
        by_cases hcq : (q.color == p.turn) = true
        · rw [if_pos hcq] at hms
          obtain ⟨hmsrc, -, -⟩ := pieceMove_spec p s q m hms
          have hqk : q.kind = .king := by
            have h1 : (p.board s).any (·.kind == .king) = true := by
              unfold isKingMove at hk
              rwa [hmsrc] at hk
            rw [hb] at h1
            exact beq_iff_eq.mp (by simpa using h1)
          obtain ⟨qc, qk⟩ := q
          cases qk with
          | pawn => exact Kind.noConfusion (show Kind.pawn = Kind.king from hqk)
          | knight =>
            simp only [pieceMoves, List.mem_map] at hms
            obtain ⟨t, -, hm'⟩ := hms
            rw [← hm']
          | bishop =>
            simp only [pieceMoves, List.mem_map] at hms
            obtain ⟨t, -, hm'⟩ := hms
            rw [← hm']
          | rook =>
            simp only [pieceMoves, List.mem_map] at hms
            obtain ⟨t, -, hm'⟩ := hms
            rw [← hm']
          | queen =>
            simp only [pieceMoves, List.mem_map] at hms
            obtain ⟨t, -, hm'⟩ := hms
            rw [← hm']
          | king =>
            simp only [pieceMoves, List.mem_map] at hms
            obtain ⟨t, -, hm'⟩ := hms
            rw [← hm']
        · rw [if_neg hcq] at hms
          exact absurd hms (not_mem_nil' m)
    · exact absurd (castleMove_isCastle p m hps) hcast

theorem isKingMove_false_of_ep (p : Pos) (m : Move) (hm : m ∈ legalMoves p) (v : Sq)
    (hv : epVictim p m = some v) : isKingMove p m = false := by
  obtain ⟨-, -, -, -, -, hsrcp⟩ := epVictim_spec p m v hm hv
  unfold isKingMove
  rw [hsrcp]
  rfl

theorem king_stay (p : Pos) (m : Move) (hm : m ∈ legalMoves p)
    (hsafe : inCheck p p.turn.opp = false) (c : Color) (K : Sq)
    (hK : p.board K = some ⟨c, .king⟩) (hks : K ≠ m.src) :
    (play p m).board K = some ⟨c, .king⟩ := by
  have hkd : K ≠ m.dst := fun hh => legal_not_capture_king p m hm hsafe c (hh ▸ hK)
  cases hv : epVictim p m with
  | some v =>
    have hkv : K ≠ v := by
      obtain ⟨-, -, hbv, -⟩ := epVictim_spec p m v hm hv
      intro hh
      rw [hh, hbv] at hK
      simp only [Option.some.injEq, Piece.mk.injEq] at hK
      exact absurd hK.2 (by decide)
    have hki : isKingMove p m = false := isKingMove_false_of_ep p m hm v hv
    have hcast : isCastle p m = false := by
      unfold isCastle
      rw [hki]
      rfl
    have he : epVictim p m ≠ some K := by
      rw [hv]
      intro hh
      exact hkv (Option.some.inj hh).symm
    rw [play_board_other p m K hks hkd he hcast]
    exact hK
  | none =>
    by_cases hcast : isCastle p m = true
    · rcases castleMove_full p m (legal_castle_mem p m hm hcast) with
        ⟨rfl, hsrc4, hr7, h5, h6⟩ | ⟨rfl, hsrc4, hr0, h3, h2⟩
      · have hks' : K ≠ sq 4 p.turn.home := hks
        have hk6 : K ≠ sq 6 p.turn.home := by
          intro hh
          rw [hh, h6] at hK
          simp at hK
        have hk5 : K ≠ sq 5 p.turn.home := by
          intro hh
          rw [hh, h5] at hK
          simp at hK
        have hk7 : K ≠ sq 7 p.turn.home := by
          intro hh
          rw [hh, hr7] at hK
          simp only [Option.some.injEq, Piece.mk.injEq] at hK
          exact absurd hK.2 (by decide)
        rw [play_board_castleK p hsrc4 K, beq_eq_false_iff_ne.mpr hk6, beq_eq_false_iff_ne.mpr hks',
          beq_eq_false_iff_ne.mpr hk5, beq_eq_false_iff_ne.mpr hk7]
        exact hK
      · have hks' : K ≠ sq 4 p.turn.home := hks
        have hk2 : K ≠ sq 2 p.turn.home := by
          intro hh
          rw [hh, h2] at hK
          simp at hK
        have hk3 : K ≠ sq 3 p.turn.home := by
          intro hh
          rw [hh, h3] at hK
          simp at hK
        have hk0 : K ≠ sq 0 p.turn.home := by
          intro hh
          rw [hh, hr0] at hK
          simp only [Option.some.injEq, Piece.mk.injEq] at hK
          exact absurd hK.2 (by decide)
        rw [play_board_castleQ p hsrc4 K, beq_eq_false_iff_ne.mpr hk2, beq_eq_false_iff_ne.mpr hks',
          beq_eq_false_iff_ne.mpr hk3, beq_eq_false_iff_ne.mpr hk0]
        exact hK
    · have he : epVictim p m ≠ some K := by
        rw [hv]
        simp
      have hcast' : isCastle p m = false := Bool.not_eq_true _ |>.mp hcast
      rw [play_board_other p m K hks hkd he hcast']
      exact hK

theorem isKingMove_true_of_board (p : Pos) (m : Move) (c : Color)
    (h : p.board m.src = some ⟨c, .king⟩) : isKingMove p m = true := by
  unfold isKingMove
  rw [h]
  rfl

theorem c0_kings_play (p : Pos) (m : Move) (hc : C0 p) (hm : m ∈ legalMoves p) :
    (∃ w, ∀ s, (play p m).board s = some ⟨.white, .king⟩ ↔ s = w) ∧
      (∃ b, ∀ s, (play p m).board s = some ⟨.black, .king⟩ ↔ s = b) := by
  obtain ⟨W, hW⟩ := hc.wk
  obtain ⟨B, hB⟩ := hc.bk
  have hWW : p.board W = some ⟨.white, .king⟩ := (hW W).mpr rfl
  have hBB : p.board B = some ⟨.black, .king⟩ := (hB B).mpr rfl
  by_cases hkm : isKingMove p m = true
  · have hksrc : p.board m.src = some ⟨p.turn, .king⟩ := kingMove_src p m hm hkm
    have hpr : m.promo = none := kingMove_promo p m hm hkm
    have hbdst : (play p m).board m.dst = some ⟨p.turn, .king⟩ := by
      rw [play_board_dst, hpr, hksrc]
    constructor
    · cases htu : p.turn with
      | white =>
        refine ⟨m.dst, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
        · rcases king_back p m hm .white s hs with ⟨hb, hsr, -⟩ | ⟨rfl, -, -⟩
          · have h1 : s = W := (hW s).mp hb
            rw [htu] at hksrc
            have h2 : m.src = W := (hW m.src).mp hksrc
            exact absurd (h1.trans h2.symm) hsr
          · rfl
        · subst hs
          rw [htu] at hbdst
          exact hbdst
      | black =>
        refine ⟨W, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
        · rcases king_back p m hm .white s hs with ⟨hb, -, -⟩ | ⟨-, hbs, -⟩
          · exact (hW s).mp hb
          · rw [htu] at hksrc
            rw [hksrc] at hbs
            simp only [Option.some.injEq, Piece.mk.injEq] at hbs
            exact absurd hbs.1 (by decide)
        · rw [hs]
          rw [htu] at hksrc
          exact king_stay p m hm hc.safe .white W hWW (fun hh => by
            rw [hh, hksrc] at hWW
            simp only [Option.some.injEq, Piece.mk.injEq] at hWW
            exact absurd hWW.1 (by decide))
    · cases htu : p.turn with
      | white =>
        refine ⟨B, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
        · rcases king_back p m hm .black s hs with ⟨hb, -, -⟩ | ⟨-, hbs, -⟩
          · exact (hB s).mp hb
          · rw [htu] at hksrc
            rw [hksrc] at hbs
            simp only [Option.some.injEq, Piece.mk.injEq] at hbs
            exact absurd hbs.1 (by decide)
        · rw [hs]
          rw [htu] at hksrc
          exact king_stay p m hm hc.safe .black B hBB (fun hh => by
            rw [hh, hksrc] at hBB
            simp only [Option.some.injEq, Piece.mk.injEq] at hBB
            exact absurd hBB.1 (by decide))
      | black =>
        refine ⟨m.dst, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
        · rcases king_back p m hm .black s hs with ⟨hb, hsr, -⟩ | ⟨rfl, -, -⟩
          · have h1 : s = B := (hB s).mp hb
            rw [htu] at hksrc
            have h2 : m.src = B := (hB m.src).mp hksrc
            exact absurd (h1.trans h2.symm) hsr
          · rfl
        · subst hs
          rw [htu] at hbdst
          exact hbdst
  · have hkm' : isKingMove p m = false := Bool.not_eq_true _ |>.mp hkm
    constructor
    · refine ⟨W, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
      · rcases king_back p m hm .white s hs with ⟨hb, -, -⟩ | ⟨-, hbs, -⟩
        · exact (hW s).mp hb
        · exact absurd (isKingMove_true_of_board p m .white hbs) (by simp [hkm'])
      · rw [hs]
        exact king_stay p m hm hc.safe .white W hWW (fun hh =>
          absurd (isKingMove_true_of_board p m .white (hh ▸ hWW)) (by simp [hkm']))
    · refine ⟨B, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
      · rcases king_back p m hm .black s hs with ⟨hb, -, -⟩ | ⟨-, hbs, -⟩
        · exact (hB s).mp hb
        · exact absurd (isKingMove_true_of_board p m .black hbs) (by simp [hkm'])
      · rw [hs]
        exact king_stay p m hm hc.safe .black B hBB (fun hh =>
          absurd (isKingMove_true_of_board p m .black (hh ▸ hBB)) (by simp [hkm']))

theorem check_of_adj_kings (p : Pos) (k1 k2 : Sq) (c : Color)
    (h1 : p.board k1 = some ⟨c, .king⟩) (h2 : p.board k2 = some ⟨c.opp, .king⟩)
    (hd : kdist k1 k2 = 1) : inCheck p c = true := by
  rw [inCheck_iff]
  refine ⟨k1, h1, (attacked_iff _ _ _).mpr ⟨k2, ⟨c.opp, .king⟩, h2, rfl, ?_⟩⟩
  rw [mem_attacks_iff]
  exact ⟨beq_iff_eq.mpr (kdist_comm k2 k1 ▸ hd),
    fun hs => absurd (show isSlider Kind.king = true from hs) (by decide)⟩

theorem c0_apart_play (p : Pos) (m : Move) (hc : C0 p) (hm : m ∈ legalMoves p) :
    ∀ w b, (play p m).board w = some ⟨.white, .king⟩ → (play p m).board b = some ⟨.black, .king⟩ →
      2 ≤ kdist w b := by
  intro w b hw hb
  suffices hh : kdist w b ≠ 0 ∧ kdist w b ≠ 1 by omega
  constructor
  · intro h0
    have h0' : (fx w - fx b).natAbs = 0 ∧ (ry w - ry b).natAbs = 0 := by
      unfold kdist at h0
      omega
    have he : w = b := sq_eq_of_coords w b (by omega) (by omega)
    rw [he, hb] at hw
    simp only [Option.some.injEq, Piece.mk.injEq] at hw
    exact absurd hw.1 (by decide)
  · intro h1
    have hcontra : inCheck (play p m) p.turn = true := by
      cases htu : p.turn with
      | white => exact check_of_adj_kings _ w b .white hw hb h1
      | black => exact check_of_adj_kings _ b w .black hb hw (kdist_comm b w ▸ h1)
    rw [legal_safe p m hm] at hcontra
    exact absurd hcontra (by decide)

theorem c0_pawns_play (p : Pos) (m : Move) (hc : C0 p) (hm : m ∈ legalMoves p) :
    ∀ s c, (play p m).board s = some ⟨c, .pawn⟩ → ry s ≠ 0 ∧ ry s ≠ 7 := by
  intro s c h
  have hsd : m.src ≠ m.dst := legal_src_ne_dst p m hm
  by_cases hdst : s = m.dst
  · subst hdst
    rw [play_board_dst] at h
    cases hpr : m.promo with
    | some k =>
      rw [hpr] at h
      cases hbs : p.board m.src with
      | none => simp [hbs] at h
      | some q =>
        rw [hbs] at h
        simp only [Option.map_some, Option.some.injEq, Piece.mk.injEq] at h
        obtain ⟨-, hkk⟩ := h
        rcases legal_promo_kind p m hm k hpr with rfl | rfl | rfl | rfl <;>
          exact absurd hkk (by decide)
    | none =>
      rw [hpr] at h
      dsimp only at h
      have hki : isKingMove p m = false := by
        unfold isKingMove
        rw [h]
        rfl
      obtain ⟨q2, hq2src, -, hmem⟩ := legal_nonking_mem p m hm hki
      rw [h] at hq2src
      obtain rfl := Option.some.inj hq2src
      have hpm : m ∈ pawnMoves p m.src c := hmem
      obtain ⟨-, hcases, hpromo⟩ := pawnMoves_cases p m.src c m hpm
      have hs1 := hc.pawns m.src c h
      have hlast : ry m.dst ≠ c.last := by
        intro hh
        have h2 := hpromo.mpr hh
        rw [hpr] at h2
        exact absurd h2 (by decide)
      rcases hcases with ⟨-, hry, -⟩ | ⟨-, hry, hph, -, -⟩ | ⟨hatt, -⟩
      · cases c with
        | white =>
          have b1 := ry_nonneg m.dst; have b2 := ry_lt m.dst
          have b3 := ry_nonneg m.src; have b4 := ry_lt m.src
          simp only [Color.fwd, Color.last] at hry hlast
          constructor <;> omega
        | black =>
          have b1 := ry_nonneg m.dst; have b2 := ry_lt m.dst
          have b3 := ry_nonneg m.src; have b4 := ry_lt m.src
          simp only [Color.fwd, Color.last] at hry hlast
          constructor <;> omega
      · cases c with
        | white =>
          have b1 := ry_nonneg m.dst; have b2 := ry_lt m.dst
          have b3 := ry_nonneg m.src; have b4 := ry_lt m.src
          simp only [Color.fwd, Color.last, Color.pawnHome] at hry hph hlast
          constructor <;> omega
        | black =>
          have b1 := ry_nonneg m.dst; have b2 := ry_lt m.dst
          have b3 := ry_nonneg m.src; have b4 := ry_lt m.src
          simp only [Color.fwd, Color.last, Color.pawnHome] at hry hph hlast
          constructor <;> omega
      · obtain ⟨hry, -⟩ := pawn_attack_geom _ _ _ _ hatt
        cases c with
        | white =>
          have b1 := ry_nonneg m.dst; have b2 := ry_lt m.dst
          have b3 := ry_nonneg m.src; have b4 := ry_lt m.src
          simp only [Color.fwd, Color.last] at hry hlast
          constructor <;> omega
        | black =>
          have b1 := ry_nonneg m.dst; have b2 := ry_lt m.dst
          have b3 := ry_nonneg m.src; have b4 := ry_lt m.src
          simp only [Color.fwd, Color.last] at hry hlast
          constructor <;> omega
  · by_cases hsrc : s = m.src
    · subst hsrc
      rw [play_board_src p m hsd] at h
      simp at h
    · cases hv : epVictim p m with
      | some v =>
        by_cases hsv : s = v
        · subst hsv
          rw [play_board_epVictim p m _ hv hdst] at h
          simp at h
        · have he : epVictim p m ≠ some s := by
            rw [hv]
            intro hh
            exact hsv (Option.some.inj hh).symm
          have hki : isKingMove p m = false := isKingMove_false_of_ep p m hm v hv
          have hcast : isCastle p m = false := by
            unfold isCastle
            rw [hki]
            rfl
          rw [play_board_other p m s hsrc hdst he hcast] at h
          exact hc.pawns s c h
      | none =>
        by_cases hcast : isCastle p m = true
        · rcases castleMove_full p m (legal_castle_mem p m hm hcast) with
            ⟨rfl, hsrc4, hr7, h5, h6⟩ | ⟨rfl, hsrc4, hr0, h3, h2⟩
          · have hdst' : s ≠ sq 6 p.turn.home := hdst
            have hsrc' : s ≠ sq 4 p.turn.home := hsrc
            by_cases hs5 : s = sq 5 p.turn.home
            · subst hs5
              rw [play_board_castleK p hsrc4 _] at h
              rw [beq_eq_false_iff_ne.mpr (sq_ne_of_file 5 6 (by decide) (by decide) _ (home_lt _) (by decide)),
                beq_eq_false_iff_ne.mpr (sq_ne_of_file 5 4 (by decide) (by decide) _ (home_lt _) (by decide)),
                beq_self_eq_true] at h
              simp only [Bool.false_eq_true, if_false, ite_true] at h
              rw [hr7] at h
              simp only [Option.some.injEq, Piece.mk.injEq] at h
              exact absurd h.2 (by decide)
            · by_cases hs7 : s = sq 7 p.turn.home
              · subst hs7
                rw [play_board_castleK p hsrc4 _] at h
                rw [beq_eq_false_iff_ne.mpr (sq_ne_of_file 7 6 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_eq_false_iff_ne.mpr (sq_ne_of_file 7 4 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_eq_false_iff_ne.mpr (sq_ne_of_file 7 5 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_self_eq_true] at h
                simp only [Bool.false_eq_true, if_false, ite_true] at h
                exact absurd h (by simp)
              · rw [play_board_castleK p hsrc4 s, beq_eq_false_iff_ne.mpr hdst',
                  beq_eq_false_iff_ne.mpr hsrc', beq_eq_false_iff_ne.mpr hs5,
                  beq_eq_false_iff_ne.mpr hs7] at h
                exact hc.pawns s c h
          · have hdst' : s ≠ sq 2 p.turn.home := hdst
            have hsrc' : s ≠ sq 4 p.turn.home := hsrc
            by_cases hs3 : s = sq 3 p.turn.home
            · subst hs3
              rw [play_board_castleQ p hsrc4 _] at h
              rw [beq_eq_false_iff_ne.mpr (sq_ne_of_file 3 2 (by decide) (by decide) _ (home_lt _) (by decide)),
                beq_eq_false_iff_ne.mpr (sq_ne_of_file 3 4 (by decide) (by decide) _ (home_lt _) (by decide)),
                beq_self_eq_true] at h
              simp only [Bool.false_eq_true, if_false, ite_true] at h
              rw [hr0] at h
              simp only [Option.some.injEq, Piece.mk.injEq] at h
              exact absurd h.2 (by decide)
            · by_cases hs0 : s = sq 0 p.turn.home
              · subst hs0
                rw [play_board_castleQ p hsrc4 _] at h
                rw [beq_eq_false_iff_ne.mpr (sq_ne_of_file 0 2 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_eq_false_iff_ne.mpr (sq_ne_of_file 0 4 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_eq_false_iff_ne.mpr (sq_ne_of_file 0 3 (by decide) (by decide) _ (home_lt _) (by decide)),
                  beq_self_eq_true] at h
                simp only [Bool.false_eq_true, if_false, ite_true] at h
                exact absurd h (by simp)
              · rw [play_board_castleQ p hsrc4 s, beq_eq_false_iff_ne.mpr hdst',
                  beq_eq_false_iff_ne.mpr hsrc', beq_eq_false_iff_ne.mpr hs3,
                  beq_eq_false_iff_ne.mpr hs0] at h
                exact hc.pawns s c h
        · have he : epVictim p m ≠ some s := by
            rw [hv]
            simp
          have hcast' : isCastle p m = false := Bool.not_eq_true _ |>.mp hcast
          rw [play_board_other p m s hsrc hdst he hcast'] at h
          exact hc.pawns s c h

theorem c0_ep_play (p : Pos) (m : Move) (hc : C0 p) (hm : m ∈ legalMoves p) :
    ∀ t, (play p m).ep = some t → epOk (play p m) t := by
  intro t ht
  rw [play_ep] at ht
  by_cases hcond : ((p.board m.src).any (·.kind == .pawn) &&
      (m.src.rank + 2 == m.dst.rank || m.dst.rank + 2 == m.src.rank)) = true
  · rw [if_pos hcond] at ht
    obtain rfl := Option.some.inj ht
    obtain ⟨hisP, hrd⟩ := Bool.and_eq_true _ _ |>.mp hcond
    obtain ⟨q, hqsrc, hqcol⟩ := legal_src p m hm
    rw [hqsrc] at hisP
    have hqk : q.kind = .pawn := beq_iff_eq.mp (by simpa using hisP)
    obtain ⟨qc, qk⟩ := q
    have hqcol' : qc = p.turn := hqcol
    have hsrcp : p.board m.src = some ⟨p.turn, .pawn⟩ := by
      cases qk with
      | pawn => rw [hqcol'] at hqsrc; exact hqsrc
      | knight => exact Kind.noConfusion (show Kind.knight = Kind.pawn from hqk)
      | bishop => exact Kind.noConfusion (show Kind.bishop = Kind.pawn from hqk)
      | rook => exact Kind.noConfusion (show Kind.rook = Kind.pawn from hqk)
      | queen => exact Kind.noConfusion (show Kind.queen = Kind.pawn from hqk)
      | king => exact Kind.noConfusion (show Kind.king = Kind.pawn from hqk)
    have hsd : m.src ≠ m.dst := legal_src_ne_dst p m hm
    have hki : isKingMove p m = false := by unfold isKingMove; rw [hsrcp]; rfl
    obtain ⟨q2, hq2src, -, hmem⟩ := legal_nonking_mem p m hm hki
    rw [hsrcp] at hq2src
    obtain rfl := Option.some.inj hq2src
    have hpm : m ∈ pawnMoves p m.src p.turn := hmem
    obtain ⟨-, hcases, hpromo⟩ := pawnMoves_cases p m.src p.turn m hpm
    have hrdA : m.src.rank + 2 = m.dst.rank ∨ m.dst.rank + 2 = m.src.rank := by
      rcases Bool.or_eq_true _ _ |>.mp hrd with hh | hh
      · exact Or.inl (beq_iff_eq.mp hh)
      · exact Or.inr (beq_iff_eq.mp hh)
    have hcast : isCastle p m = false := by unfold isCastle; rw [hki]; rfl
    have hfilt : m.src.file < 8 := Nat.mod_lt _ (by decide)
    cases htu : p.turn with
    | white =>
      rcases hcases with ⟨hfx1, hry1, -⟩ | ⟨hfx2, hry2, hph, -, hseg⟩ | ⟨hatt, -⟩
      · exfalso
        have h2 : ry m.dst = ry m.src + 1 := by simpa [htu, Color.fwd] using hry1
        have rd : (m.dst.rank : Int) = m.src.rank + 1 := h2
        omega
      · have hr1 : ry m.src = 1 := by simpa [htu, Color.pawnHome] using hph
        have hr3 : ry m.dst = 3 := by
          have h2 : ry m.dst = ry m.src + 2 * 1 := by simpa [htu, Color.fwd] using hry2
          omega
        have hsrk : m.src.rank = 1 := by
          have e : (m.src.rank : Int) = 1 := hr1
          omega
        have hdrk : m.dst.rank = 3 := by
          have e : (m.dst.rank : Int) = 3 := hr3
          omega
        have hmid : (m.src.rank + m.dst.rank) / 2 = 2 := by rw [hsrk, hdrk]
        rw [hmid]
        have hft : fx (sq m.src.file 2) = fx m.src := fx_sq m.src.file 2 hfilt (by decide)
        have hrt : ry (sq m.src.file 2) = 2 := ry_sq m.src.file 2 hfilt (by decide)
        have hfil : m.dst.file = m.src.file := by
          have e : (m.dst.file : Int) = (m.src.file : Int) := hfx2
          omega
        have hve : epVictim p m = none := by
          have hni : ¬((p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file &&
              empty p.board m.dst) = true := by
            intro hh
            obtain ⟨h1, -⟩ := Bool.and_eq_true _ _ |>.mp hh
            obtain ⟨-, hb⟩ := Bool.and_eq_true _ _ |>.mp h1
            rw [bne_iff_ne] at hb
            exact hb hfil.symm
          unfold epVictim
          rw [if_neg hni]
        have htne1 : sq m.src.file 2 ≠ m.src := sq_ne_of_coords _ _ (Or.inr (by rw [hrt, hr1]; decide))
        have htne2 : sq m.src.file 2 ≠ m.dst := sq_ne_of_coords _ _ (Or.inr (by rw [hrt, hr3]; decide))
        have hsegT : inSeg m.src m.dst (sq m.src.file 2) = true :=
          step_seg m.src m.dst (sq m.src.file 2) ((0 : Int), (1 : Int)) (by decide) 2 1
            (by decide) (by decide) (by decide)
            (by simpa using hfx2) (by rw [hr3, hr1]; decide)
            (by simpa using hft) (by rw [hrt, hr1]; decide)
        unfold epOk
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ry (sq m.src.file 2) = (if (play p m).turn = Color.white then (5 : Int) else 2)
          rw [play_turn, htu]
          show ry (sq m.src.file 2) = (2 : Int)
          exact hrt
        · rw [play_board_other p m _ htne1 htne2 (by rw [hve]; simp) hcast]
          exact hseg _ hsegT
        · refine ⟨m.src, ?_, ?_⟩
          · rw [play_turn, htu]
            apply (off_eq_some _ _ _ _).mpr
            show fx m.src = fx (sq m.src.file 2) + (0 : Int) ∧ ry m.src = ry (sq m.src.file 2) + (-1 : Int)
            rw [hft, hrt]
            constructor
            · rw [Int.add_zero]
            · rw [hr1]
              decide
          · exact play_board_src p m hsd
        · refine ⟨m.dst, ?_, ?_⟩
          · rw [play_turn, htu]
            apply (off_eq_some _ _ _ _).mpr
            show fx m.dst = fx (sq m.src.file 2) + (0 : Int) ∧ ry m.dst = ry (sq m.src.file 2) + (1 : Int)
            rw [hft, hrt]
            constructor
            · rw [Int.add_zero]
              exact hfx2
            · rw [hr3]
              decide
          · have hpr2 : m.promo = none := by
              cases hpmpr : m.promo with
              | none => rfl
              | some k =>
                exfalso
                have h7 := hpromo.mp (by rw [hpmpr]; rfl)
                rw [htu] at h7
                simp only [Color.last] at h7
                rw [hr3] at h7
                exact absurd h7 (by decide)
            rw [play_board_dst, hpr2, hsrcp, play_turn, htu]
            rfl
      · exfalso
        obtain ⟨hry3, -⟩ := pawn_attack_geom _ _ _ _ hatt
        have h2 : ry m.dst = ry m.src + 1 := by simpa [htu, Color.fwd] using hry3
        have rd : (m.dst.rank : Int) = m.src.rank + 1 := h2
        omega
    | black =>
      rcases hcases with ⟨hfx1, hry1, -⟩ | ⟨hfx2, hry2, hph, -, hseg⟩ | ⟨hatt, -⟩
      · exfalso
        have h2 : ry m.dst = ry m.src + -1 := by simpa [htu, Color.fwd] using hry1
        have rd : (m.dst.rank : Int) = m.src.rank + -1 := h2
        omega
      · have hr6 : ry m.src = 6 := by simpa [htu, Color.pawnHome] using hph
        have hr4 : ry m.dst = 4 := by
          have h2 : ry m.dst = ry m.src + 2 * -1 := by simpa [htu, Color.fwd] using hry2
          omega
        have hsrk : m.src.rank = 6 := by
          have e : (m.src.rank : Int) = 6 := hr6
          omega
        have hdrk : m.dst.rank = 4 := by
          have e : (m.dst.rank : Int) = 4 := hr4
          omega
        have hmid : (m.src.rank + m.dst.rank) / 2 = 5 := by rw [hsrk, hdrk]
        rw [hmid]
        have hft : fx (sq m.src.file 5) = fx m.src := fx_sq m.src.file 5 hfilt (by decide)
        have hrt : ry (sq m.src.file 5) = 5 := ry_sq m.src.file 5 hfilt (by decide)
        have hfil : m.dst.file = m.src.file := by
          have e : (m.dst.file : Int) = (m.src.file : Int) := hfx2
          omega
        have hve : epVictim p m = none := by
          have hni : ¬((p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file &&
              empty p.board m.dst) = true := by
            intro hh
            obtain ⟨h1, -⟩ := Bool.and_eq_true _ _ |>.mp hh
            obtain ⟨-, hb⟩ := Bool.and_eq_true _ _ |>.mp h1
            rw [bne_iff_ne] at hb
            exact hb hfil.symm
          unfold epVictim
          rw [if_neg hni]
        have htne1 : sq m.src.file 5 ≠ m.src := sq_ne_of_coords _ _ (Or.inr (by rw [hrt, hr6]; decide))
        have htne2 : sq m.src.file 5 ≠ m.dst := sq_ne_of_coords _ _ (Or.inr (by rw [hrt, hr4]; decide))
        have hsegT : inSeg m.src m.dst (sq m.src.file 5) = true :=
          step_seg m.src m.dst (sq m.src.file 5) ((0 : Int), (-1 : Int)) (by decide) 2 1
            (by decide) (by decide) (by decide)
            (by simpa using hfx2) (by rw [hr4, hr6]; decide)
            (by simpa using hft) (by rw [hrt, hr6]; decide)
        unfold epOk
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ry (sq m.src.file 5) = (if (play p m).turn = Color.white then (5 : Int) else 2)
          rw [play_turn, htu]
          show ry (sq m.src.file 5) = (5 : Int)
          exact hrt
        · rw [play_board_other p m _ htne1 htne2 (by rw [hve]; simp) hcast]
          exact hseg _ hsegT
        · refine ⟨m.src, ?_, ?_⟩
          · rw [play_turn, htu]
            apply (off_eq_some _ _ _ _).mpr
            show fx m.src = fx (sq m.src.file 5) + (0 : Int) ∧ ry m.src = ry (sq m.src.file 5) + (1 : Int)
            rw [hft, hrt]
            constructor
            · rw [Int.add_zero]
            · rw [hr6]
              decide
          · exact play_board_src p m hsd
        · refine ⟨m.dst, ?_, ?_⟩
          · rw [play_turn, htu]
            apply (off_eq_some _ _ _ _).mpr
            show fx m.dst = fx (sq m.src.file 5) + (0 : Int) ∧ ry m.dst = ry (sq m.src.file 5) + (-1 : Int)
            rw [hft, hrt]
            constructor
            · rw [Int.add_zero]
              exact hfx2
            · rw [hr4]
              decide
          · have hpr2 : m.promo = none := by
              cases hpmpr : m.promo with
              | none => rfl
              | some k =>
                exfalso
                have h0 := hpromo.mp (by rw [hpmpr]; rfl)
                rw [htu] at h0
                simp only [Color.last] at h0
                rw [hr4] at h0
                exact absurd h0 (by decide)
            rw [play_board_dst, hpr2, hsrcp, play_turn, htu]
            rfl
      · exfalso
        obtain ⟨hry3, -⟩ := pawn_attack_geom _ _ _ _ hatt
        have h2 : ry m.dst = ry m.src + -1 := by simpa [htu, Color.fwd] using hry3
        have rd : (m.dst.rank : Int) = m.src.rank + -1 := h2
        omega
  · rw [if_neg hcond] at ht
    exact absurd ht (by simp)

theorem c0_play (p : Pos) (m : Move) (hc : C0 p) (hm : m ∈ legalMoves p) : C0 (play p m) :=
  ⟨(c0_kings_play p m hc hm).1, (c0_kings_play p m hc hm).2, c0_apart_play p m hc hm,
    c0_pawns_play p m hc hm,
    by
      rw [play_turn, Color.opp_opp]
      exact legal_safe p m hm,
    c0_ep_play p m hc hm⟩

theorem reachable_c0 (p : Pos) (h : Reachable p) : C0 p := by
  induction h with
  | init => exact initial_c0
  | step _ hm ih => exact c0_play _ _ ih hm

theorem c0_after_legal (p : Pos) (ms : List Move) (hc : C0 p)
    (hl : ∀ i (h : i < ms.length), ms[i] ∈ legalMoves (after p (ms.take i))) : C0 (after p ms) := by
  induction ms generalizing p with
  | nil => exact hc
  | cons m ms ih =>
    have h0 : m ∈ legalMoves p := by
      have h1 := hl 0 (by simp)
      simpa [after] using h1
    apply ih (play p m) (c0_play p m hc h0)
    intro i hi
    have h1 := hl (i + 1) (by simp [List.length_cons]; omega)
    rw [List.getElem_cons_succ, List.take_succ_cons] at h1
    exact h1

theorem nodupFinRange : ∀ n : Nat, (List.finRange n).Nodup := by
  intro n
  induction n with
  | zero => rw [List.finRange_zero]; exact List.nodup_nil
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    refine ⟨?_, List.Pairwise.map Fin.succ (fun _ _ h h' => h (Fin.succ_inj.mp h')) ih⟩
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨a, -, ha⟩ := hm
    exact Fin.succ_ne_zero a ha

theorem nodup_allSq : allSq.Nodup := nodupFinRange 64

theorem length_filter_sum (l : List Sq) (f : Sq → Bool) :
    (l.filter f).length = (l.map fun s => if f s = true then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : (f a = true)
    · rw [List.filter_cons_of_pos h, List.length_cons, List.map_cons, List.sum_cons, if_pos h, ih]
      omega
    · rw [List.filter_cons_of_neg h, List.map_cons, List.sum_cons, if_neg h, Nat.zero_add, ih]

def nkI (b : Board) (s : Sq) : Nat := if (b s).any (·.kind != .king) = true then 1 else 0

theorem bne_king_val (k : Kind) :
    (if (k != .king) = true then (1 : Nat) else 0) = if k = .king then 0 else 1 := by
  cases k <;> decide

theorem pawnKind_ne_king (c : Color) : (⟨c, Kind.pawn⟩ : Piece).kind ≠ Kind.king :=
  fun h => Kind.noConfusion (show Kind.pawn = Kind.king from h)

theorem rookKind_ne_king (c : Color) : (⟨c, Kind.rook⟩ : Piece).kind ≠ Kind.king :=
  fun h => Kind.noConfusion (show Kind.rook = Kind.king from h)

theorem nkI_of_none {b : Board} {s : Sq} (h : b s = none) : nkI b s = 0 := by
  show (if (b s).any (·.kind != .king) = true then (1 : Nat) else 0) = 0
  rw [h]
  rfl

theorem nkI_neking {b : Board} {s : Sq} {q : Piece} (h : b s = some q) (hk : q.kind ≠ .king) :
    nkI b s = 1 := by
  show (if (b s).any (·.kind != .king) = true then (1 : Nat) else 0) = 1
  rw [h, Option.any_some]
  exact if_pos (bne_iff_ne.mpr hk)

theorem nkI_king {b : Board} {s : Sq} {q : Piece} (h : b s = some q) (hk : q.kind = .king) :
    nkI b s = 0 := by
  show (if (b s).any (·.kind != .king) = true then (1 : Nat) else 0) = 0
  rw [h, Option.any_some]
  exact if_neg (fun hh => bne_iff_ne.mp hh hk)

theorem nkI_some_ite {b : Board} {s : Sq} {q : Piece} (h : b s = some q) :
    nkI b s = if q.kind = .king then 0 else 1 := by
  by_cases hk : q.kind = .king
  · rw [if_pos hk]
    exact nkI_king h hk
  · rw [if_neg hk]
    exact nkI_neking h hk

theorem nonKing_sum (p : Pos) : nonKing p = (allSq.map (nkI p.board)).sum :=
  length_filter_sum allSq _

theorem sum_map_congr (l : List Sq) (f g : Sq → Nat) (h : ∀ s ∈ l, f s = g s) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      h a List.mem_cons_self, ih fun s hs => h s (List.mem_cons_of_mem a hs)]

theorem sum_map_pt {l : List Sq} (hl : l.Nodup) (f g : Sq → Nat) (x : Sq) (hx : x ∈ l)
    (h : ∀ s ∈ l, s ≠ x → f s = g s) :
    (l.map f).sum + g x = (l.map g).sum + f x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨ha, hln⟩ := hl
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
        sum_map_congr l f g fun s hs => h s (List.mem_cons_of_mem _ hs) (fun hsx => by
          subst hsx; exact absurd hs ha)]
      omega
    · have hax : a ≠ x := fun hax => ha (hax ▸ hx)
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
        h a List.mem_cons_self hax]
      have e := ih hln hx fun s hs hsx => h s (List.mem_cons_of_mem a hs) hsx
      omega

theorem sum_map_pt2 {l : List Sq} (hl : l.Nodup) (f g : Sq → Nat) (x y : Sq) (hxy : x ≠ y)
    (hx : x ∈ l) (hy : y ∈ l) (h : ∀ s ∈ l, s ≠ x → s ≠ y → f s = g s) :
    (l.map f).sum + g x + g y = (l.map g).sum + f x + f y := by
  have hmidx : (if x = x then f x else g x) = f x := if_pos rfl
  have hmidy : (if y = x then f x else g y) = g y := if_neg fun hyx => hxy hyx.symm
  have h1 := sum_map_pt hl (fun s => if s = x then f x else g s) g x hx fun s hs hsx => if_neg hsx
  have h2 := sum_map_pt hl f (fun s => if s = x then f x else g s) y hy fun s hs hsy => by
    by_cases hsx : s = x
    · subst hsx
      exact (if_pos rfl).symm
    · exact (h s hs hsx hsy).trans (if_neg hsx).symm
  rw [hmidx] at h1
  rw [hmidy] at h2
  omega

theorem sum_map_pt3 {l : List Sq} (hl : l.Nodup) (f g : Sq → Nat) (x y z : Sq)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : x ∈ l) (hy : y ∈ l) (hz : z ∈ l)
    (h : ∀ s ∈ l, s ≠ x → s ≠ y → s ≠ z → f s = g s) :
    (l.map f).sum + g x + g y + g z = (l.map g).sum + f x + f y + f z := by
  have hmidz : (if z = z then f z else g z) = f z := if_pos rfl
  have hmidx : (if x = z then f z else g x) = g x := if_neg hxz
  have hmidy : (if y = z then f z else g y) = g y := if_neg hyz
  have h1 := sum_map_pt hl (fun s => if s = z then f z else g s) g z hz fun s hs hsz => if_neg hsz
  have h2 := sum_map_pt2 hl f (fun s => if s = z then f z else g s) x y hxy hx hy fun s hs hsx hsy => by
    by_cases hsz : s = z
    · subst hsz
      exact (if_pos rfl).symm
    · exact (h s hs hsx hsy hsz).trans (if_neg hsz).symm
  rw [hmidz] at h1
  rw [hmidx, hmidy] at h2
  omega

theorem nonKing_initial : nonKing initial = 30 := by
  decide

theorem nonKing_play (p : Pos) (m : Move) (hc : C0 p) (hm : m ∈ legalMoves p) :
    nonKing (play p m) + (if isCapture p m then 1 else 0) = nonKing p := by
  rw [nonKing_sum p, nonKing_sum (play p m)]
  obtain ⟨q, hqsrc, -⟩ := legal_src p m hm
  have hsd : m.src ≠ m.dst := legal_src_ne_dst p m hm
  have hFsrc : nkI (play p m).board m.src = 0 := nkI_of_none (play_board_src p m hsd)
  have hGsrc : nkI p.board m.src = if q.kind = .king then 0 else 1 := nkI_some_ite hqsrc
  cases hv : epVictim p m with
  | some v =>
    obtain ⟨-, hdn, hbv, -, -, hsrcp⟩ := epVictim_spec p m v hm hv
    have hki : isKingMove p m = false := by
      show (p.board m.src).any (·.kind == .king) = false
      rw [hsrcp]
      rfl
    have hcast' : isCastle p m = false := by
      unfold isCastle
      rw [hki]
      rfl
    have hvd : v ≠ m.dst := by
      intro hV
      rw [hV, hdn] at hbv
      simp at hbv
    have hsv : m.src ≠ v := by
      intro hV
      rw [hV, hbv] at hsrcp
      have h2 := Option.some.inj hsrcp
      rw [Piece.mk.injEq] at h2
      exact absurd h2.1 (by cases p.turn <;> decide)
    have hGsrc1 : nkI p.board m.src = 1 := nkI_neking hsrcp (pawnKind_ne_king _)
    have hGv : nkI p.board v = 1 := nkI_neking hbv (pawnKind_ne_king _)
    have hGdst0 : nkI p.board m.dst = 0 := nkI_of_none hdn
    have hFv : nkI (play p m).board v = 0 := nkI_of_none (play_board_epVictim p m v hv hvd)
    have hFdst : nkI (play p m).board m.dst = 1 := by
      cases hpr : m.promo with
      | none =>
        have hbd : (play p m).board m.dst = p.board m.src := by rw [play_board_dst, hpr]
        exact nkI_neking (hbd.trans hsrcp) (pawnKind_ne_king _)
      | some k =>
        have hknk : k ≠ .king := by
          have h1 := promo_ne_king p m (legal_mem_pseudo p m hm)
          rw [hpr] at h1
          exact fun h2 => h1 (congrArg some h2)
        have hbd : (play p m).board m.dst = some ⟨p.turn, k⟩ := by
          rw [play_board_dst, hpr, hsrcp]
          rfl
        exact nkI_neking hbd hknk
    have hagree : ∀ s ∈ allSq, s ≠ m.src → s ≠ v → s ≠ m.dst →
        nkI (play p m).board s = nkI p.board s := by
      intro s hs h1 h2 h3
      show (if ((play p m).board s).any (·.kind != .king) = true then (1 : Nat) else 0) =
        if (p.board s).any (·.kind != .king) = true then 1 else 0
      have he : epVictim p m ≠ some s := by
        rw [hv]
        exact fun hh => h2 (Option.some.inj hh).symm
      rw [play_board_other p m s h1 h3 he hcast']
    have hcf : isCapture p m = true := by
      show ((p.board m.dst).isSome || (epVictim p m).isSome) = true
      rw [hdn, hv]
      rfl
    have hcapit : (if isCapture p m then (1 : Nat) else 0) = 1 := by
      show (if isCapture p m = true then (1 : Nat) else 0) = 1
      rw [hcf]
      rfl
    have hsurg := sum_map_pt3 nodup_allSq (nkI (play p m).board) (nkI p.board) m.src v m.dst
      hsv hsd hvd (mem_allSq _) (mem_allSq _) (mem_allSq _) hagree
    rw [hGsrc1, hGv, hGdst0, hFsrc, hFv, hFdst] at hsurg
    rw [hcapit]
    omega
  | none =>
    by_cases hcast : isCastle p m = true
    · rcases castleMove_full p m (legal_castle_mem p m hm hcast) with
        ⟨hmeq, hsrc4, hr7, h5, h6⟩ | ⟨hmeq, hsrc4, hr0, h3, h2⟩
      · subst hmeq
        have hnt : ¬ (false = true) := fun hh => Bool.noConfusion hh
        have ht : (true = true) := rfl
        have ne46 : sq 4 p.turn.home ≠ sq 6 p.turn.home :=
          sq_ne_of_file 4 6 (by decide) (by decide) _ (home_lt _) (by decide)
        have ne56 : sq 5 p.turn.home ≠ sq 6 p.turn.home :=
          sq_ne_of_file 5 6 (by decide) (by decide) _ (home_lt _) (by decide)
        have ne54 : sq 5 p.turn.home ≠ sq 4 p.turn.home :=
          sq_ne_of_file 5 4 (by decide) (by decide) _ (home_lt _) (by decide)
        have ne76 : sq 7 p.turn.home ≠ sq 6 p.turn.home :=
          sq_ne_of_file 7 6 (by decide) (by decide) _ (home_lt _) (by decide)
        have ne74 : sq 7 p.turn.home ≠ sq 4 p.turn.home :=
          sq_ne_of_file 7 4 (by decide) (by decide) _ (home_lt _) (by decide)
        have ne75 : sq 7 p.turn.home ≠ sq 5 p.turn.home :=
          sq_ne_of_file 7 5 (by decide) (by decide) _ (home_lt _) (by decide)
        have hG7 : nkI p.board (sq 7 p.turn.home) = 1 := nkI_neking hr7 (rookKind_ne_king _)
        have hG5 : nkI p.board (sq 5 p.turn.home) = 0 := nkI_of_none h5
        have hG6 : nkI p.board (sq 6 p.turn.home) = 0 := nkI_of_none h6
        have hG4 : nkI p.board (sq 4 p.turn.home) = 0 := nkI_king hsrc4 rfl
        have e6 : (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board (sq 6 p.turn.home) =
            p.board (sq 4 p.turn.home) := by
          rw [play_board_castleK p hsrc4 _, beq_self_eq_true]
          exact if_pos ht
        have e4 : (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board (sq 4 p.turn.home) =
            none := by
          rw [play_board_castleK p hsrc4 _, beq_eq_false_iff_ne.mpr ne46, beq_self_eq_true]
          rw [if_neg hnt, if_pos ht]
        have e5 : (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board (sq 5 p.turn.home) =
            p.board (sq 7 p.turn.home) := by
          rw [play_board_castleK p hsrc4 _, beq_eq_false_iff_ne.mpr ne56,
            beq_eq_false_iff_ne.mpr ne54, beq_self_eq_true]
          rw [if_neg hnt, if_neg hnt, if_pos ht]
        have e7 : (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board (sq 7 p.turn.home) =
            none := by
          rw [play_board_castleK p hsrc4 _, beq_eq_false_iff_ne.mpr ne76,
            beq_eq_false_iff_ne.mpr ne74, beq_eq_false_iff_ne.mpr ne75, beq_self_eq_true]
          rw [if_neg hnt, if_neg hnt, if_neg hnt, if_pos ht]
        have hF7 : nkI (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board
            (sq 7 p.turn.home) = 0 := nkI_of_none e7
        have hF5 : nkI (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board
            (sq 5 p.turn.home) = 1 := nkI_neking (e5.trans hr7) (rookKind_ne_king _)
        have hF6 : nkI (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board
            (sq 6 p.turn.home) = 0 := nkI_king (e6.trans hsrc4) rfl
        have hF4 : nkI (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board
            (sq 4 p.turn.home) = 0 := nkI_of_none e4
        have hagree : ∀ s ∈ allSq, s ≠ sq 7 p.turn.home → s ≠ sq 5 p.turn.home →
            nkI (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board s = nkI p.board s := by
          intro z hz hne7 hne5
          by_cases h6z : z = sq 6 p.turn.home
          · subst h6z
            rw [hF6, hG6]
          · by_cases h4z : z = sq 4 p.turn.home
            · subst h4z
              rw [hF4, hG4]
            · show (if ((play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board z).any
                    (·.kind != .king) = true then (1 : Nat) else 0) =
                  if (p.board z).any (·.kind != .king) = true then 1 else 0
              rw [play_board_castleK p hsrc4 z, beq_eq_false_iff_ne.mpr h6z,
                beq_eq_false_iff_ne.mpr h4z, beq_eq_false_iff_ne.mpr hne5,
                beq_eq_false_iff_ne.mpr hne7]
              rw [if_neg hnt, if_neg hnt, if_neg hnt, if_neg hnt]
        have hany : (p.board (Move.src ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩)).any
            (·.kind == .pawn) = false := by
          show (p.board (sq 4 p.turn.home)).any (·.kind == .pawn) = false
          rw [hsrc4]
          rfl
        have hepgen : epVictim p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ = none := by
          unfold epVictim
          apply if_neg
          intro hh
          rw [hany, Bool.false_and] at hh
          exact Bool.noConfusion hh
        have hcf : isCapture p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ = false := by
          show ((p.board (sq 6 p.turn.home)).isSome ||
            (epVictim p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).isSome) = false
          rw [h6, hepgen]
          rfl
        have hcapit : (if isCapture p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ then (1 : Nat)
            else 0) = 0 := by
          show (if isCapture p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ = true then (1 : Nat)
            else 0) = 0
          rw [hcf]
          exact if_neg hnt
        have hsurg := sum_map_pt2 nodup_allSq
          (nkI (play p ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩).board) (nkI p.board)
          (sq 7 p.turn.home) (sq 5 p.turn.home) ne75 (mem_allSq _) (mem_allSq _) hagree
        rw [hG7, hG5, hF7, hF5] at hsurg
        rw [hcapit]
        omega
      · subst hmeq
        have hnt : ¬ (false = true) := fun hh => Bool.noConfusion hh
        have ht : (true = true) := rfl
        have ne42 : sq 4 p.turn.home ≠ sq 2 p.turn.home :=
          sq_ne_of_file 4 2 (by decide) (by decide) _ (home_lt _) (by decide)
        have ne34 : sq 3 p.turn.home ≠ sq 4 p.turn.home :=
          sq_ne_of_file 3 4 (by decide) (by decide) _ (home_lt _) (by decide)
        have ne32 : sq 3 p.turn.home ≠ sq 2 p.turn.home :=
          sq_ne_of_file 3 2 (by decide) (by decide) _ (home_lt _) (by decide)
        have ne02 : sq 0 p.turn.home ≠ sq 2 p.turn.home :=
          sq_ne_of_file 0 2 (by decide) (by decide) _ (home_lt _) (by decide)
        have ne04 : sq 0 p.turn.home ≠ sq 4 p.turn.home :=
          sq_ne_of_file 0 4 (by decide) (by decide) _ (home_lt _) (by decide)
        have ne03 : sq 0 p.turn.home ≠ sq 3 p.turn.home :=
          sq_ne_of_file 0 3 (by decide) (by decide) _ (home_lt _) (by decide)
        have hG0 : nkI p.board (sq 0 p.turn.home) = 1 := nkI_neking hr0 (rookKind_ne_king _)
        have hG3 : nkI p.board (sq 3 p.turn.home) = 0 := nkI_of_none h3
        have hG2 : nkI p.board (sq 2 p.turn.home) = 0 := nkI_of_none h2
        have hG4 : nkI p.board (sq 4 p.turn.home) = 0 := nkI_king hsrc4 rfl
        have e2 : (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board (sq 2 p.turn.home) =
            p.board (sq 4 p.turn.home) := by
          rw [play_board_castleQ p hsrc4 _, beq_self_eq_true]
          exact if_pos ht
        have e4 : (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board (sq 4 p.turn.home) =
            none := by
          rw [play_board_castleQ p hsrc4 _, beq_eq_false_iff_ne.mpr ne42, beq_self_eq_true]
          rw [if_neg hnt, if_pos ht]
        have e3 : (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board (sq 3 p.turn.home) =
            p.board (sq 0 p.turn.home) := by
          rw [play_board_castleQ p hsrc4 _, beq_eq_false_iff_ne.mpr ne32,
            beq_eq_false_iff_ne.mpr ne34, beq_self_eq_true]
          rw [if_neg hnt, if_neg hnt, if_pos ht]
        have e0 : (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board (sq 0 p.turn.home) =
            none := by
          rw [play_board_castleQ p hsrc4 _, beq_eq_false_iff_ne.mpr ne02,
            beq_eq_false_iff_ne.mpr ne04, beq_eq_false_iff_ne.mpr ne03, beq_self_eq_true]
          rw [if_neg hnt, if_neg hnt, if_neg hnt, if_pos ht]
        have hF0 : nkI (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board
            (sq 0 p.turn.home) = 0 := nkI_of_none e0
        have hF3 : nkI (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board
            (sq 3 p.turn.home) = 1 := nkI_neking (e3.trans hr0) (rookKind_ne_king _)
        have hF2 : nkI (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board
            (sq 2 p.turn.home) = 0 := nkI_king (e2.trans hsrc4) rfl
        have hF4 : nkI (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board
            (sq 4 p.turn.home) = 0 := nkI_of_none e4
        have hagree : ∀ s ∈ allSq, s ≠ sq 0 p.turn.home → s ≠ sq 3 p.turn.home →
            nkI (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board s = nkI p.board s := by
          intro z hz hne0 hne3
          by_cases h2z : z = sq 2 p.turn.home
          · subst h2z
            rw [hF2, hG2]
          · by_cases h4z : z = sq 4 p.turn.home
            · subst h4z
              rw [hF4, hG4]
            · show (if ((play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board z).any
                    (·.kind != .king) = true then (1 : Nat) else 0) =
                  if (p.board z).any (·.kind != .king) = true then 1 else 0
              rw [play_board_castleQ p hsrc4 z, beq_eq_false_iff_ne.mpr h2z,
                beq_eq_false_iff_ne.mpr h4z, beq_eq_false_iff_ne.mpr hne3,
                beq_eq_false_iff_ne.mpr hne0]
              rw [if_neg hnt, if_neg hnt, if_neg hnt, if_neg hnt]
        have hany : (p.board (Move.src ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩)).any
            (·.kind == .pawn) = false := by
          show (p.board (sq 4 p.turn.home)).any (·.kind == .pawn) = false
          rw [hsrc4]
          rfl
        have hepgen : epVictim p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ = none := by
          unfold epVictim
          apply if_neg
          intro hh
          rw [hany, Bool.false_and] at hh
          exact Bool.noConfusion hh
        have hcf : isCapture p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ = false := by
          show ((p.board (sq 2 p.turn.home)).isSome ||
            (epVictim p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).isSome) = false
          rw [h2, hepgen]
          rfl
        have hcapit : (if isCapture p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ then (1 : Nat)
            else 0) = 0 := by
          show (if isCapture p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ = true then (1 : Nat)
            else 0) = 0
          rw [hcf]
          exact if_neg hnt
        have hsurg := sum_map_pt2 nodup_allSq
          (nkI (play p ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩).board) (nkI p.board)
          (sq 0 p.turn.home) (sq 3 p.turn.home) ne03 (mem_allSq _) (mem_allSq _) hagree
        rw [hG0, hG3, hF0, hF3] at hsurg
        rw [hcapit]
        omega
    · have hcast' : isCastle p m = false := Bool.not_eq_true _ |>.mp hcast
      have hFdst : nkI (play p m).board m.dst = if q.kind = .king then 0 else 1 := by
        cases hpr : m.promo with
        | none =>
          have hbd : (play p m).board m.dst = p.board m.src := by rw [play_board_dst, hpr]
          exact nkI_some_ite (hbd.trans hqsrc)
        | some k =>
          have hknk : k ≠ .king := by
            have h1 := promo_ne_king p m (legal_mem_pseudo p m hm)
            rw [hpr] at h1
            exact fun h2 => h1 (congrArg some h2)
          have hkq : q.kind ≠ .king := by
            intro hkk
            have hki : isKingMove p m = true := by
              show (p.board m.src).any (·.kind == .king) = true
              rw [hqsrc]
              exact beq_iff_eq.mpr hkk
            have h2 := kingMove_promo p m hm hki
            rw [hpr] at h2
            simp at h2
          have hbd : (play p m).board m.dst = some ⟨q.color, k⟩ := by
            rw [play_board_dst, hpr, hqsrc]
            rfl
          rw [nkI_neking hbd hknk, if_neg hkq]
      have hGdst : nkI p.board m.dst = (if (p.board m.dst).isSome = true then (1 : Nat) else 0) := by
        cases hbd : p.board m.dst with
        | none =>
          show (if (p.board m.dst).any (·.kind != .king) = true then (1 : Nat) else 0) = _
          rw [hbd]
          rfl
        | some r =>
          have hrk : r.kind ≠ .king := by
            intro hkr
            have heta : r = ⟨r.color, r.kind⟩ := rfl
            rw [hkr] at heta
            have hbd2 : p.board m.dst = some ⟨r.color, .king⟩ := heta ▸ hbd
            exact dst_ne_king p m hm hc.safe r.color hbd2
          show (if (p.board m.dst).any (·.kind != .king) = true then (1 : Nat) else 0) = _
          rw [hbd]
          exact if_pos (bne_iff_ne.mpr hrk)
      have hcf : isCapture p m = (p.board m.dst).isSome := by
        show ((p.board m.dst).isSome || (epVictim p m).isSome) = (p.board m.dst).isSome
        rw [hv]
        show ((p.board m.dst).isSome || false) = (p.board m.dst).isSome
        exact Bool.or_false _
      have hcapit : (if isCapture p m then (1 : Nat) else 0) =
          (if (p.board m.dst).isSome = true then 1 else 0) := by
        show (if isCapture p m = true then (1 : Nat) else 0) = _
        rw [hcf]
      have hagree : ∀ s ∈ allSq, s ≠ m.src → s ≠ m.dst →
          nkI (play p m).board s = nkI p.board s := by
        intro s hs h1 h3
        show (if ((play p m).board s).any (·.kind != .king) = true then (1 : Nat) else 0) =
          if (p.board s).any (·.kind != .king) = true then 1 else 0
        rw [play_board_other p m s h1 h3 (by rw [hv]; exact fun hh => by simp at hh) hcast']
      have hsurg := sum_map_pt2 nodup_allSq (nkI (play p m).board) (nkI p.board) m.src m.dst
        hsd (mem_allSq _) (mem_allSq _) hagree
      rw [hGsrc, hGdst, hFsrc, hFdst] at hsurg
      rw [hcapit]
      omega

theorem nonKing_reachable (p : Pos) (h : Reachable p) : nonKing p ≤ 30 := by
  induction h with
  | init =>
    have e := nonKing_initial
    omega
  | step hr hm ih =>
    have e := nonKing_play _ _ (reachable_c0 _ hr) hm
    omega

theorem nonKing_pos_of_check (p : Pos) (hc : C0 p) (h : inCheck p p.turn = true) : 1 ≤ nonKing p := by
  obtain ⟨k, hk, hatt⟩ := (inCheck_iff p p.turn).mp h
  rw [attacked_iff] at hatt
  obtain ⟨t, q, ht, hqcol, hmem⟩ := hatt
  have hqk : q.kind ≠ .king := by
    intro hkk
    have heta : q = ⟨q.color, q.kind⟩ := rfl
    rw [hkk] at heta
    rw [heta] at hmem
    have hd1 : kdist t k = 1 := king_attack_adjacent p.board t k q.color hmem
    cases htu : p.turn with
    | white =>
      rw [htu] at hk
      rw [heta] at ht
      rw [hqcol, htu] at ht
      have h2 := hc.apart k t hk ht
      rw [kdist_comm t k] at hd1
      omega
    | black =>
      rw [htu] at hk
      rw [heta] at ht
      rw [hqcol, htu] at ht
      have h2 := hc.apart t k ht hk
      omega
  have hmemf : t ∈ allSq.filter fun s => (p.board s).any (·.kind != .king) :=
    List.mem_filter.mpr ⟨mem_allSq t, by
      rw [ht, Option.any_some]
      show (q.kind != .king) = true
      exact bne_iff_ne.mpr hqk⟩
  exact List.length_pos_of_mem hmemf

end Chess.C364
