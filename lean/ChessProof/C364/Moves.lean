import ChessProof.C364.Attack

namespace Chess.C364

open Chess

theorem play_turn (p : Pos) (m : Move) : (play p m).turn = p.turn.opp := by
  rfl

theorem Color.opp_opp (c : Color) : c.opp.opp = c := by
  cases c <;> rfl

theorem play_board_dst (p : Pos) (m : Move) :
    (play p m).board m.dst = (match m.promo with
      | some k => (p.board m.src).map fun q => ⟨q.color, k⟩
      | none => p.board m.src) := by
  cases h : m.promo <;> simp [play, h]

theorem play_board_src (p : Pos) (m : Move) (h : m.src ≠ m.dst) : (play p m).board m.src = none := by
  unfold play
  dsimp only
  simp [beq_iff_eq, h]

theorem play_board_other (p : Pos) (m : Move) (s : Sq) (hs : s ≠ m.src) (hd : s ≠ m.dst)
    (he : epVictim p m ≠ some s) (hc : isCastle p m = false) : (play p m).board s = p.board s := by
  have hc1 : ((p.board m.src).any (·.kind == .king) && m.src.file + 2 == m.dst.file) = false := by
    cases hf : (m.src.file + 2 == m.dst.file) <;> simp_all [isCastle, isKingMove]
  have hc2 : ((p.board m.src).any (·.kind == .king) && m.dst.file + 2 == m.src.file) = false := by
    cases hf : (m.dst.file + 2 == m.src.file) <;> simp_all [isCastle, isKingMove]
  have hev : ((if (p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file &&
        empty p.board m.dst then some (sq m.dst.file m.src.rank) else none) == some s) = false := by
    unfold epVictim at he
    by_cases hC : ((p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file &&
        empty p.board m.dst) = true
    · rw [if_pos hC] at he ⊢
      simp_all
    · rw [if_neg hC] at he ⊢
      rfl
  unfold play
  dsimp only
  simp only [hc1, hc2, hev]
  simp [beq_iff_eq, hs, hd]

theorem play_board_epVictim (p : Pos) (m : Move) (v : Sq) (h : epVictim p m = some v) (hd : v ≠ m.dst) :
    (play p m).board v = none := by
  have hc : ((p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file &&
      empty p.board m.dst) = true := by
    unfold epVictim at h
    split at h
    · assumption
    · contradiction
  have hv : sq m.dst.file m.src.rank = v := by
    unfold epVictim at h
    split at h
    · exact Option.some.inj h
    · contradiction
  unfold play
  dsimp only
  simp [beq_iff_eq, hd, hc, hv]

theorem legal_mem_pseudo (p : Pos) (m : Move) (h : m ∈ legalMoves p) : m ∈ pseudo p := by
  unfold legalMoves at h
  exact (List.mem_filter.mp h).1

theorem legal_safe (p : Pos) (m : Move) (h : m ∈ legalMoves p) : inCheck (play p m) p.turn = false := by
  unfold legalMoves at h
  rw [List.mem_filter] at h
  simpa using h.2

theorem opt_filter_eq_some {α : Type} (g : α → Bool) (o : Option α) (a : α) :
    o.filter g = some a ↔ o = some a ∧ g a = true := by
  cases o with
  | none => simp [Option.filter]
  | some x =>
    by_cases hg : g x = true
    · simp only [Option.filter, if_pos hg, Option.some.injEq]
      constructor
      · intro h
        rw [← h]
        exact ⟨rfl, hg⟩
      · exact And.left
    · simp only [Option.filter, if_neg hg]
      constructor
      · intro h
        contradiction
      · intro h
        rw [Option.some.inj h.1] at hg
        exact absurd h.2 hg

theorem not_mem_nil' {α : Type} (a : α) : a ∉ ([] : List α) := by simp

theorem off_ne_self (s t : Sq) (df dr : Int) (h : off s df dr = some t) (hd : df ≠ 0 ∨ dr ≠ 0) :
    t ≠ s := by
  obtain ⟨hf, hr⟩ := (off_eq_some s t df dr).mp h
  apply sq_ne_of_coords
  rcases hd with hd | hd
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem empty_eq_none (b : Board) (t : Sq) (h : empty b t = true) : b t = none := by
  cases hb : b t with
  | none => rfl
  | some q => simp [empty, hb] at h

theorem foe_ne (b : Board) (c : Color) (t : Sq) (h : foe b c t = true) :
    ∀ q, b t = some q → q.color ≠ c := by
  intro q hq
  simp [foe, hq] at h
  intro hc
  rw [hc] at h
  simp at h

theorem epCap_none (p : Pos) (c : Color) (t : Sq) (h : epCap p c t = true) : p.board t = none := by
  unfold epCap at h
  obtain ⟨h1, -⟩ := Bool.and_eq_true _ _ |>.mp h
  exact empty_eq_none _ _ (Bool.and_eq_true _ _ |>.mp h1).2

theorem pawnMove_gen (s : Sq) (c : Color) (m : Move) (t : Sq)
    (h : m ∈ (if t.rank == c.last then
      [Kind.knight, .bishop, .rook, .queen].map fun k => ⟨s, t, some k⟩ else [⟨s, t, none⟩])) :
    m.src = s ∧ m.dst = t := by
  by_cases hL : (t.rank == c.last) = true
  · rw [if_pos hL, List.mem_map] at h
    obtain ⟨k, _, hk⟩ := h
    obtain rfl := hk
    exact ⟨rfl, rfl⟩
  · rw [if_neg hL] at h
    rw [List.mem_singleton] at h
    obtain rfl := h
    exact ⟨rfl, rfl⟩

theorem pawnMove_spec (p : Pos) (s : Sq) (c : Color) (m : Move) (h : m ∈ pawnMoves p s c) :
    m.src = s ∧ m.dst ≠ s ∧ (∀ q, p.board m.dst = some q → q.color ≠ c) := by
  have hfw : c.fwd ≠ 0 := by cases c <;> decide
  unfold pawnMoves at h
  dsimp only at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, Option.mem_toList,
    List.mem_filter, opt_filter_eq_some] at h
  rcases h with ⟨t, ht, hm⟩ | ⟨t, ht, hm⟩
  · obtain ⟨h1, h2⟩ := pawnMove_gen s c m t hm
    refine ⟨h1, ?_, ?_⟩
    · rcases ht with ht | ht
      · exact h2.symm ▸ off_ne_self s t 0 c.fwd ht.1 (Or.inr hfw)
      · obtain ⟨hts, -⟩ := ht
        rw [mem_steps] at hts
        obtain ⟨d, hd, hf, -⟩ := hts
        subst h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        apply sq_ne_of_coords
        rcases hd with rfl | rfl
        · have hf' : fx m.dst = fx s + 1 := hf
          exact Or.inl (by omega)
        · have hf' : fx m.dst = fx s + -1 := hf
          exact Or.inl (by omega)
    · rcases ht with ht | ht
      · have hn := empty_eq_none _ _ ht.2
        intro q hq
        rw [h2, hn] at hq
        contradiction
      · obtain ⟨-, hfc⟩ := ht
        intro q hq
        rw [h2] at hq
        obtain hf | he := Bool.or_eq_true _ _ |>.mp hfc
        · exact foe_ne _ _ _ hf _ hq
        · rw [epCap_none _ _ _ he] at hq
          contradiction
  · obtain rfl := hm
    have hts : off s 0 (2 * c.fwd) = some t ∧ empty p.board t = true := by
      by_cases hcond : (s.rank == c.pawnHome && ((off s 0 c.fwd).filter (empty p.board)).isSome) = true
      · rw [if_pos hcond, opt_filter_eq_some] at ht
        exact ht
      · rw [if_neg hcond] at ht
        contradiction
    refine ⟨rfl, ?_, ?_⟩
    · exact off_ne_self s t 0 (2 * c.fwd) hts.1 (Or.inr (by cases c <;> decide))
    · intro q hq
      rw [empty_eq_none _ _ hts.2] at hq
      contradiction

theorem pieceMove_spec (p : Pos) (s : Sq) (q : Piece) (m : Move) (h : m ∈ pieceMoves p s q) :
    m.src = s ∧ m.dst ≠ s ∧ (∀ q2, p.board m.dst = some q2 → q2.color ≠ q.color) := by
  obtain ⟨cc, kk⟩ := q
  cases kk
  · change m ∈ pawnMoves p s cc at h
    exact pawnMove_spec p s cc m h
  all_goals
    unfold pieceMoves at h
    dsimp only at h
    rw [List.mem_map] at h
    obtain ⟨t, ht, hm⟩ := h
    obtain rfl := hm
    rw [List.mem_filter] at ht
    obtain ⟨hta, hto⟩ := ht
    refine ⟨rfl, fun he => attacks_ne _ _ _ _ hta he, ?_⟩
    intro q2 hq2
    rw [hq2] at hto
    simp at hto
    intro hc
    rw [hc] at hto
    simp at hto

theorem sq_ne_of_file (f1 f2 : Nat) (hf1 : f1 < 8) (hf2 : f2 < 8) (r : Nat) (_hr : r < 8)
    (hne : f1 ≠ f2) : sq f1 r ≠ sq f2 r := by
  intro hh
  have hv := congrArg Fin.val hh
  simp only [sq] at hv
  omega

theorem home_lt (c : Color) : c.home < 8 := by cases c <;> decide

theorem castleMove_spec (p : Pos) (m : Move) (h : m ∈ castleMoves p) :
    m.src = sq 4 p.turn.home ∧ p.board m.src = some ⟨p.turn, .king⟩ ∧
    p.board m.dst = none ∧ (m.dst = sq 6 p.turn.home ∨ m.dst = sq 2 p.turn.home) := by
  unfold castleMoves at h
  dsimp only at h
  by_cases hout : ((p.board (sq 4 p.turn.home) == some ⟨p.turn, .king⟩) &&
      !attacked p.board (sq 4 p.turn.home) p.turn.opp) = true
  · rw [if_pos hout, List.mem_append] at h
    obtain ⟨hk, -⟩ := Bool.and_eq_true _ _ |>.mp hout
    have hke : p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ := beq_iff_eq.mp hk
    rcases h with h | h
    · by_cases hK : ((p.castleK p.turn && p.board (sq 7 p.turn.home) == some ⟨p.turn, .rook⟩ &&
        [5, 6].all fun f => empty p.board (sq f p.turn.home)) &&
        !attacked p.board (sq 5 p.turn.home) p.turn.opp) = true
      · rw [if_pos hK, List.mem_singleton] at h
        obtain rfl := h
        obtain ⟨hf, -⟩ := Bool.and_eq_true _ _ |>.mp hK
        obtain ⟨-, hf⟩ := Bool.and_eq_true _ _ |>.mp hf
        have h6 : empty p.board (sq 6 p.turn.home) = true := by
          rw [List.all_eq_true] at hf
          exact hf 6 (by simp)
        exact ⟨rfl, hke, empty_eq_none _ _ h6, Or.inl rfl⟩
      · rw [if_neg hK] at h
        exact absurd h (not_mem_nil' m)
    · by_cases hQ : ((p.castleQ p.turn && p.board (sq 0 p.turn.home) == some ⟨p.turn, .rook⟩ &&
        [1, 2, 3].all fun f => empty p.board (sq f p.turn.home)) &&
        !attacked p.board (sq 3 p.turn.home) p.turn.opp) = true
      · rw [if_pos hQ, List.mem_singleton] at h
        obtain rfl := h
        obtain ⟨hf, -⟩ := Bool.and_eq_true _ _ |>.mp hQ
        obtain ⟨-, hf⟩ := Bool.and_eq_true _ _ |>.mp hf
        have h2 : empty p.board (sq 2 p.turn.home) = true := by
          rw [List.all_eq_true] at hf
          exact hf 2 (by simp)
        exact ⟨rfl, hke, empty_eq_none _ _ h2, Or.inr rfl⟩
      · rw [if_neg hQ] at h
        exact absurd h (not_mem_nil' m)
  · rw [if_neg hout] at h
    exact absurd h (not_mem_nil' m)

theorem pseudo_spec (p : Pos) (m : Move) (h : m ∈ pseudo p) :
    (∃ q, p.board m.src = some q ∧ q.color = p.turn) ∧ m.src ≠ m.dst ∧
    (∀ q, p.board m.dst = some q → q.color ≠ p.turn) := by
  unfold pseudo at h
  rw [List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨s, _, hm⟩ := h
    match hb : p.board s with
    | none =>
      rw [hb] at hm
      exact absurd hm (not_mem_nil' m)
    | some q =>
      rw [hb] at hm
      dsimp only at hm
      by_cases hc : (q.color == p.turn) = true
      · rw [if_pos hc] at hm
        obtain ⟨h1, h2, h3⟩ := pieceMove_spec p s q m hm
        have hq : q.color = p.turn := beq_iff_eq.mp hc
        exact ⟨⟨q, h1.symm ▸ hb, hq⟩,
          fun he => h2 (h1 ▸ he).symm,
          fun q2 hq2 => hq ▸ h3 q2 hq2⟩
      · rw [if_neg hc] at hm
        exact absurd hm (not_mem_nil' m)
  · obtain ⟨h1, h2, h3, h4⟩ := castleMove_spec p m h
    refine ⟨⟨⟨p.turn, .king⟩, h1 ▸ h2, rfl⟩, ?_, ?_⟩
    · intro he
      rw [h1] at he
      rcases h4 with h4 | h4
      · rw [h4] at he
        exact sq_ne_of_file 4 6 (by decide) (by decide) p.turn.home (home_lt _) (by decide) he
      · rw [h4] at he
        exact sq_ne_of_file 4 2 (by decide) (by decide) p.turn.home (home_lt _) (by decide) he
    · intro q2 hq2
      rw [h3] at hq2
      contradiction

theorem legal_src (p : Pos) (m : Move) (h : m ∈ legalMoves p) :
    ∃ q, p.board m.src = some q ∧ q.color = p.turn :=
  (pseudo_spec p m (legal_mem_pseudo p m h)).1

theorem legal_src_ne_dst (p : Pos) (m : Move) (h : m ∈ legalMoves p) : m.src ≠ m.dst :=
  (pseudo_spec p m (legal_mem_pseudo p m h)).2.1

theorem legal_dst_not_own (p : Pos) (m : Move) (h : m ∈ legalMoves p) (q : Piece)
    (hq : p.board m.dst = some q) : q.color ≠ p.turn :=
  (pseudo_spec p m (legal_mem_pseudo p m h)).2.2 q hq

theorem file_sq (f r : Nat) (hf : f < 8) (hr : r < 8) : (sq f r).file = f := by
  have h1 : (r * 8 + f) % 64 = r * 8 + f := Nat.mod_eq_of_lt (by omega)
  show ((r * 8 + f) % 64) % 8 = f
  rw [h1]
  omega

theorem rank_sq (f r : Nat) (hf : f < 8) (hr : r < 8) : (sq f r).rank = r := by
  have h1 : (r * 8 + f) % 64 = r * 8 + f := Nat.mod_eq_of_lt (by omega)
  show ((r * 8 + f) % 64) / 8 = r
  rw [h1]
  omega

theorem mem_pieceMoves_nonpawn (p : Pos) (s : Sq) (q : Piece) (m : Move)
    (hm : m ∈ pieceMoves p s q) (hk : q.kind ≠ .pawn) :
    m.src = s ∧ m.promo = none ∧ m.dst ∈ attacks p.board s q := by
  rcases q with ⟨c, k⟩
  cases k
  · exact absurd rfl hk
  all_goals
    unfold pieceMoves at hm
    dsimp only at hm
    rw [List.mem_map] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    refine ⟨rfl, rfl, ?_⟩
    rw [List.mem_filter] at ht
    exact ht.1

theorem kingMove_true_of_board (p : Pos) (c : Color) (s : Sq)
    (h : p.board s = some ⟨c, .king⟩) (m : Move) (hs : m.src = s) : isKingMove p m = true := by
  show (p.board m.src).any (·.kind == .king) = true
  rw [hs, h]
  rfl

theorem legal_nonking_mem (p : Pos) (m : Move) (h : m ∈ legalMoves p) (hk : isKingMove p m = false) :
    ∃ q, p.board m.src = some q ∧ q.color = p.turn ∧ m ∈ pieceMoves p m.src q := by
  have hp := legal_mem_pseudo p m h
  unfold pseudo at hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · rw [List.mem_flatMap] at hp
    obtain ⟨s, _, hm⟩ := hp
    match hb : p.board s with
    | none =>
      rw [hb] at hm
      exact absurd hm (not_mem_nil' m)
    | some q =>
      rw [hb] at hm
      dsimp only at hm
      by_cases hc : (q.color == p.turn) = true
      · rw [if_pos hc] at hm
        obtain ⟨h1, -, -⟩ := pieceMove_spec p s q m hm
        exact ⟨q, h1.symm ▸ hb, beq_iff_eq.mp hc, h1.symm ▸ hm⟩
      · rw [if_neg hc] at hm
        exact absurd hm (not_mem_nil' m)
  · obtain ⟨h1, h2, -, -⟩ := castleMove_spec p m hp
    rw [kingMove_true_of_board p _ _ h2 m rfl] at hk
    simp at hk

theorem legal_castle_mem (p : Pos) (m : Move) (h : m ∈ legalMoves p) (hc : isCastle p m = true) :
    m ∈ castleMoves p := by
  have hp := legal_mem_pseudo p m h
  unfold pseudo at hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · exfalso
    rw [List.mem_flatMap] at hp
    obtain ⟨s, _, hm⟩ := hp
    match hb : p.board s with
    | none =>
      rw [hb] at hm
      exact absurd hm (not_mem_nil' m)
    | some q =>
      rw [hb] at hm
      dsimp only at hm
      by_cases hcc : (q.color == p.turn) = true
      · rw [if_pos hcc] at hm
        obtain ⟨h1, -, -⟩ := pieceMove_spec p s q m hm
        unfold isCastle at hc
        rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hc
        obtain ⟨hki, hfl⟩ := hc
        have hki2 : (p.board m.src).any (·.kind == .king) = true := hki
        rw [h1, hb] at hki2
        have hkk : (q.kind == .king) = true := hki2
        have hkk' : q.kind = .king := beq_iff_eq.mp hkk
        rcases q with ⟨c0, k0⟩
        have hkk3 : k0 = .king := hkk'
        subst hkk3
        obtain ⟨-, -, hatt⟩ := mem_pieceMoves_nonpawn p s ⟨c0, .king⟩ m hm (fun hh => by simp at hh)
        have hkd : kdist m.src m.dst = 1 := by
          rw [h1]
          exact king_attack_adjacent p.board s m.dst c0 hatt
        have hfm : m.src.file < 8 := Nat.mod_lt _ (by decide)
        have hfd : m.dst.file < 8 := Nat.mod_lt _ (by decide)
        unfold kdist at hkd
        have e1 : fx m.src = (m.src.file : Int) := rfl
        have e2 : fx m.dst = (m.dst.file : Int) := rfl
        rcases hfl with hfl | hfl <;> omega
      · rw [if_neg hcc] at hm
        exact absurd hm (not_mem_nil' m)
  · exact hp

theorem castleMoves_not_in_check (p : Pos) (hc0 : C0 p) (m : Move) (h : m ∈ castleMoves p) :
    inCheck p p.turn = false := by
  unfold castleMoves at h
  dsimp only at h
  by_cases hout : ((p.board (sq 4 p.turn.home) == some ⟨p.turn, .king⟩) &&
      !attacked p.board (sq 4 p.turn.home) p.turn.opp) = true
  · obtain ⟨hk, hsafe⟩ := Bool.and_eq_true _ _ |>.mp hout
    have hke : p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ := beq_iff_eq.mp hk
    have hatt : ¬ (attacked p.board (sq 4 p.turn.home) p.turn.opp = true) := by
      intro hh
      rw [hh] at hsafe
      simp at hsafe
    rw [if_pos hout, List.mem_append] at h
    cases hic : inCheck p p.turn with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨k, hkk, hakk⟩ := (inCheck_iff p p.turn).mp hic
      cases ht : p.turn with
      | white =>
        obtain ⟨w, hw⟩ := hc0.wk
        rw [ht] at hkk hke hatt hakk
        have hk_eq : k = w := (hw k).mp hkk
        have he_eq : sq 4 Color.white.home = w := (hw _).mp hke
        rw [hk_eq, ← he_eq] at hakk
        exact hatt hakk
      | black =>
        obtain ⟨b, hb⟩ := hc0.bk
        rw [ht] at hkk hke hatt hakk
        have hk_eq : k = b := (hb k).mp hkk
        have he_eq : sq 4 Color.black.home = b := (hb _).mp hke
        rw [hk_eq, ← he_eq] at hakk
        exact hatt hakk
  · rw [if_neg hout] at h
    exact absurd h (not_mem_nil' m)

theorem legal_king_step (p : Pos) (m : Move) (h : m ∈ legalMoves p) (hk : isKingMove p m = true)
    (hc : isCastle p m = false) : kdist m.src m.dst = 1 := by
  have hp := legal_mem_pseudo p m h
  unfold pseudo at hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · rw [List.mem_flatMap] at hp
    obtain ⟨s, _, hm⟩ := hp
    match hb : p.board s with
    | none =>
      rw [hb] at hm
      exact absurd hm (not_mem_nil' m)
    | some q =>
      rw [hb] at hm
      dsimp only at hm
      by_cases hcc : (q.color == p.turn) = true
      · rw [if_pos hcc] at hm
        obtain ⟨h1, -, -⟩ := pieceMove_spec p s q m hm
        have hki2 : (p.board m.src).any (·.kind == .king) = true := hk
        rw [h1, hb] at hki2
        have hkk : (q.kind == .king) = true := hki2
        have hkk' : q.kind = .king := beq_iff_eq.mp hkk
        rcases q with ⟨c0, k0⟩
        have hkk3 : k0 = .king := hkk'
        subst hkk3
        obtain ⟨-, -, hatt⟩ := mem_pieceMoves_nonpawn p s ⟨c0, .king⟩ m hm (fun hh => by simp at hh)
        rw [h1]
        exact king_attack_adjacent p.board s m.dst c0 hatt
      · rw [if_neg hcc] at hm
        exact absurd hm (not_mem_nil' m)
  · obtain ⟨h1, h2, -, h4⟩ := castleMove_spec p m hp
    have hhome : p.turn.home < 8 := home_lt _
    have e : (m.src.file + 2 == m.dst.file || m.dst.file + 2 == m.src.file) = true := by
      rcases h4 with h4 | h4
      · rw [h1, h4, file_sq 4 _ (by decide) hhome, file_sq 6 _ (by decide) hhome]
        rfl
      · rw [h1, h4, file_sq 4 _ (by decide) hhome, file_sq 2 _ (by decide) hhome]
        rfl
    have hki : (isKingMove p m && (m.src.file + 2 == m.dst.file || m.dst.file + 2 == m.src.file)) = true := by
      rw [hk, e]
      rfl
    have hcf : isCastle p m = true := hki
    rw [hcf] at hc
    simp at hc

theorem pieceMoves_geom (p : Pos) (s : Sq) (q : Piece) (m : Move) (h : m ∈ pieceMoves p s q)
    (hk : q.kind ≠ .pawn) : m.src = s ∧ m.promo = none ∧ m.dst ∈ attacks p.board s q :=
  mem_pieceMoves_nonpawn p s q m h hk

theorem pawnMove_promo (s : Sq) (c : Color) (m : Move) (t : Sq)
    (h : m ∈ (if t.rank == c.last then [Kind.knight, .bishop, .rook, .queen].map fun k => ⟨s, t, some k⟩
      else [⟨s, t, none⟩])) :
    m.src = s ∧ m.dst = t ∧ (m.promo.isSome = true ↔ ry m.dst = c.last) := by
  by_cases hL : (t.rank == c.last) = true
  · rw [if_pos hL, List.mem_map] at h
    obtain ⟨k, _, hk⟩ := h
    obtain rfl := hk.symm
    have hlast : t.rank = c.last := beq_iff_eq.mp hL
    refine ⟨rfl, rfl, fun _ => ?_, fun _ => rfl⟩
    have e2 : ((t.rank : Int)) = ((c.last : Nat) : Int) := congrArg Int.ofNat hlast
    exact e2
  · rw [if_neg hL, List.mem_singleton] at h
    obtain rfl := h
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro hh
      simp at hh
    · intro hh
      have e2 : ((t.rank : Int)) = ((c.last : Nat) : Int) := hh
      have e : t.rank = c.last := Int.ofNat_inj.mp e2
      exact absurd (beq_iff_eq.mpr e) hL

theorem pawnMoves_cases (p : Pos) (s : Sq) (c : Color) (m : Move) (h : m ∈ pawnMoves p s c) :
    m.src = s ∧
      ((fx m.dst = fx s ∧ ry m.dst = ry s + c.fwd ∧ p.board m.dst = none) ∨
       (fx m.dst = fx s ∧ ry m.dst = ry s + 2 * c.fwd ∧ ry s = c.pawnHome ∧ p.board m.dst = none ∧
          ∀ z, inSeg s m.dst z = true → p.board z = none) ∨
       (m.dst ∈ attacks p.board s ⟨c, .pawn⟩ ∧ (foe p.board c m.dst = true ∨ epCap p c m.dst = true))) ∧
      (m.promo.isSome = true ↔ ry m.dst = c.last) := by
  unfold pawnMoves at h
  dsimp only at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, Option.mem_toList,
    List.mem_filter, opt_filter_eq_some] at h
  rcases h with ⟨t, ht, hm⟩ | ⟨t, ht, hm⟩
  · obtain ⟨h1, h2, h3⟩ := pawnMove_promo s c m t hm
    subst h1
    subst h2
    refine ⟨rfl, ?_, h3⟩
    rcases ht with ht | ht
    · obtain ⟨hof, hem⟩ := ht
      obtain ⟨hfx, hry⟩ := (off_eq_some m.src m.dst 0 c.fwd).mp hof
      refine Or.inl ⟨?_, hry, empty_eq_none _ _ hem⟩
      omega
    · obtain ⟨hst, hfc⟩ := ht
      have hatt : m.dst ∈ attacks p.board m.src ⟨c, .pawn⟩ := hst
      exact Or.inr (Or.inr ⟨hatt, Bool.or_eq_true _ _ |>.mp hfc⟩)
  · obtain rfl := hm
    by_cases hcond : (s.rank == c.pawnHome && ((off s 0 c.fwd).filter (empty p.board)).isSome) = true
    · rw [if_pos hcond, opt_filter_eq_some] at ht
      obtain ⟨hof, hem⟩ := ht
      obtain ⟨hfx, hry⟩ := (off_eq_some s t 0 (2 * c.fwd)).mp hof
      obtain ⟨hhome, hone⟩ := Bool.and_eq_true _ _ |>.mp hcond
      have hhome' : s.rank = c.pawnHome := beq_iff_eq.mp hhome
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hone
      rw [opt_filter_eq_some] at hu
      obtain ⟨huo, hue⟩ := hu
      obtain ⟨hux, hur⟩ := (off_eq_some s u 0 c.fwd).mp huo
      have hu_none : p.board u = none := empty_eq_none _ _ hue
      have hfx' : fx t = fx s := by omega
      refine ⟨rfl, Or.inr (Or.inl ⟨hfx', hry, ?_, empty_eq_none _ _ hem, ?_⟩), ?_⟩
      · show ((s.rank : Nat) : Int) = ((c.pawnHome : Nat) : Int)
        rw [hhome']
      · intro z hz
        simp only [inSeg, onLine, aligned, collinear, kdist, Bool.and_eq_true, bne_iff_ne,
          beq_iff_eq, Bool.or_eq_true] at hz
        obtain ⟨h4z, hkd⟩ := hz
        obtain ⟨h3z, hz_t⟩ := h4z
        obtain ⟨h2z, hz_s⟩ := h3z
        obtain ⟨h1z, hcoll⟩ := h2z
        obtain ⟨-, -⟩ := h1z
        have e1 : ry t - ry s = 2 * c.fwd := by omega
        have e0 : fx t - fx s = 0 := by omega
        rw [e1, e0] at hcoll
        have hf : c.fwd = 1 ∨ c.fwd = -1 := by cases c <;> decide
        rcases hf with hh | hh
        · rw [hh] at hcoll hry
          have hzfx : fx z = fx s := by omega
          have hne1 : ry z ≠ ry s := fun h2 => hz_s (sq_eq_of_coords z s hzfx h2)
          have hne2 : ry z ≠ ry t := fun h2 => hz_t (sq_eq_of_coords z t (by omega) h2)
          have hzry : ry z = ry s + 1 := by
            have b3 := ry_nonneg s; have b4 := ry_lt s
            have b5 := ry_nonneg t; have b6 := ry_lt t
            have b9 := ry_nonneg z; have b10 := ry_lt z
            omega
          have hzu : z = u := sq_eq_of_coords z u (by omega) (by omega)
          rw [hzu]
          exact hu_none
        · rw [hh] at hcoll hry
          have hzfx : fx z = fx s := by omega
          have hne1 : ry z ≠ ry s := fun h2 => hz_s (sq_eq_of_coords z s hzfx h2)
          have hne2 : ry z ≠ ry t := fun h2 => hz_t (sq_eq_of_coords z t (by omega) h2)
          have hzry : ry z = ry s - 1 := by
            have b3 := ry_nonneg s; have b4 := ry_lt s
            have b5 := ry_nonneg t; have b6 := ry_lt t
            have b9 := ry_nonneg z; have b10 := ry_lt z
            omega
          have hzu : z = u := sq_eq_of_coords z u (by omega) (by omega)
          rw [hzu]
          exact hu_none
      · constructor
        · intro hh2
          simp at hh2
        · intro hh2
          have e : ((s.rank : Nat) : Int) = ((c.pawnHome : Nat) : Int) := by rw [hhome']
          have e' : ry s = ((c.pawnHome : Nat) : Int) := e
          cases c <;> simp only [Color.fwd, Color.pawnHome, Color.last] at hry e' hh2 <;> omega
    · rw [if_neg hcond] at ht
      contradiction

theorem epVictim_spec (p : Pos) (m : Move) (v : Sq) (h : m ∈ legalMoves p) (hv : epVictim p m = some v) :
    p.ep = some m.dst ∧ p.board m.dst = none ∧ p.board v = some ⟨p.turn.opp, .pawn⟩ ∧
      fx v = fx m.dst ∧ ry v = ry m.src ∧ (p.board m.src) = some ⟨p.turn, .pawn⟩ := by
  unfold epVictim at hv
  by_cases hcond : ((p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file &&
      empty p.board m.dst) = true
  · rw [if_pos hcond] at hv
    obtain ⟨hAB, hC⟩ := Bool.and_eq_true _ _ |>.mp hcond
    obtain ⟨hA, hB⟩ := Bool.and_eq_true _ _ |>.mp hAB
    obtain rfl := Option.some.inj hv
    obtain ⟨q, hq, -⟩ := legal_src p m h
    have hA' : (q.kind == .pawn) = true := by
      have e := hA
      rw [hq] at e
      exact e
    have hkp : q.kind = .pawn := beq_iff_eq.mp hA'
    have hki : isKingMove p m = false := by
      show (p.board m.src).any (·.kind == .king) = false
      rw [hq]
      change (q.kind == .king) = false
      rw [hkp]
      rfl
    obtain ⟨q', hq', hcq, hmem⟩ := legal_nonking_mem p m h hki
    rw [hq] at hq'
    obtain rfl := Option.some.inj hq'
    rcases q with ⟨c0, k0⟩
    have hkp2 : k0 = .pawn := hkp
    subst hkp2
    have hc0 : c0 = p.turn := hcq
    subst hc0
    have hmem2 : m ∈ pawnMoves p m.src p.turn := hmem
    obtain ⟨-, hdisj, -⟩ := pawnMoves_cases p m.src p.turn m hmem2
    have hfiles : m.src.file ≠ m.dst.file := bne_iff_ne.mp hB
    have hfxne : fx m.src ≠ fx m.dst := by
      intro hfx
      have hfx2 : ((m.src.file : Nat) : Int) = ((m.dst.file : Nat) : Int) := hfx
      exact hfiles (Int.ofNat_inj.mp hfx2)
    have hnone : p.board m.dst = none := empty_eq_none _ _ hC
    rcases hdisj with hd1 | hd2 | hd3
    · exact absurd hd1.1.symm hfxne
    · exact absurd hd2.1.symm hfxne
    · obtain ⟨hatt, hfl | hec⟩ := hd3
      · exfalso
        unfold foe at hfl
        rw [hnone] at hfl
        simp at hfl
      · unfold epCap at hec
        rw [Bool.and_eq_true, Bool.and_eq_true] at hec
        obtain ⟨⟨hep, -⟩, hbehind⟩ := hec
        have hep' : p.ep = some m.dst := beq_iff_eq.mp hep
        cases hof : off m.dst 0 (-p.turn.fwd) with
        | none =>
          rw [hof] at hbehind
          simp at hbehind
        | some u =>
          rw [hof] at hbehind
          have hu_pawn : p.board u = some ⟨p.turn.opp, .pawn⟩ := beq_iff_eq.mp hbehind
          obtain ⟨huxf, hury⟩ := (off_eq_some m.dst u 0 (-p.turn.fwd)).mp hof
          obtain ⟨hgeom, -⟩ := pawn_attack_geom p.board m.src m.dst p.turn hatt
          have hbd_lt : m.dst.file < 8 := Nat.mod_lt _ (by decide)
          have hsr_lt : m.src.rank < 8 := by
            have hs := m.src.isLt
            show m.src.val / 8 < 8
            omega
          have hfxv : fx (sq m.dst.file m.src.rank) = fx m.dst := by
            have e := file_sq m.dst.file m.src.rank hbd_lt hsr_lt
            show ((sq m.dst.file m.src.rank).file : Int) = ((m.dst.file : Nat) : Int)
            exact_mod_cast e
          have hryv : ry (sq m.dst.file m.src.rank) = ry m.src := by
            have e := rank_sq m.dst.file m.src.rank hbd_lt hsr_lt
            show ((sq m.dst.file m.src.rank).rank : Int) = ((m.src.rank : Nat) : Int)
            exact_mod_cast e
          have huv : u = sq m.dst.file m.src.rank := sq_eq_of_coords _ _ (by omega) (by omega)
          exact ⟨hep', hnone, huv ▸ hu_pawn, hfxv, hryv, hq⟩
  · rw [if_neg hcond] at hv
    contradiction

theorem play_ep (p : Pos) (m : Move) :
    (play p m).ep = if (p.board m.src).any (·.kind == .pawn) &&
        (m.src.rank + 2 == m.dst.rank || m.dst.rank + 2 == m.src.rank) then
      some (sq m.src.file ((m.src.rank + m.dst.rank) / 2)) else none := by
  rfl

theorem color_eq_opp_of_ne (a b : Color) (h : a ≠ b) : a = b.opp := by
  cases a <;> cases b <;> simp_all [Color.opp]

theorem pawnMove_mem_kind (s : Sq) (c : Color) (m : Move) (t : Sq)
    (h : m ∈ (if t.rank == c.last then [Kind.knight, .bishop, .rook, .queen].map fun k => ⟨s, t, some k⟩
      else [⟨s, t, none⟩])) :
    m.promo ≠ some .king := by
  by_cases hL : (t.rank == c.last) = true
  · rw [if_pos hL, List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    intro hh
    have e : k = .king := Option.some.inj hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp at e
  · rw [if_neg hL, List.mem_singleton] at h
    obtain rfl := h
    intro hh
    simp at hh

theorem promo_ne_king (p : Pos) (m : Move) (h : m ∈ pseudo p) : m.promo ≠ some .king := by
  unfold pseudo at h
  rw [List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨s, _, hm⟩ := h
    match hb : p.board s with
    | none =>
      rw [hb] at hm
      exact absurd hm (not_mem_nil' m)
    | some q =>
      rw [hb] at hm
      dsimp only at hm
      by_cases hc : (q.color == p.turn) = true
      · rw [if_pos hc] at hm
        rcases q with ⟨c0, k0⟩
        cases k0
        · change m ∈ pawnMoves p s c0 at hm
          unfold pawnMoves at hm
          dsimp only at hm
          rw [List.mem_append] at hm
          rcases hm with hm | hm
          · rw [List.mem_flatMap] at hm
            obtain ⟨t, -, hmk⟩ := hm
            exact pawnMove_mem_kind s c0 m t hmk
          · rw [List.mem_map] at hm
            obtain ⟨t, -, hmt⟩ := hm
            obtain rfl := hmt
            intro hh
            simp at hh
        all_goals
          obtain ⟨-, hpr, -⟩ := mem_pieceMoves_nonpawn p s _ m hm (fun he => by simp at he)
          rw [hpr]
          intro hh
          simp at hh
      · rw [if_neg hc] at hm
        exact absurd hm (not_mem_nil' m)
  · unfold castleMoves at h
    dsimp only at h
    by_cases hout : ((p.board (sq 4 p.turn.home) == some ⟨p.turn, .king⟩) &&
        !attacked p.board (sq 4 p.turn.home) p.turn.opp) = true
    · rw [if_pos hout, List.mem_append] at h
      rcases h with h | h
      · by_cases hK : ((p.castleK p.turn && p.board (sq 7 p.turn.home) == some ⟨p.turn, .rook⟩ &&
          [5, 6].all fun f => empty p.board (sq f p.turn.home)) &&
          !attacked p.board (sq 5 p.turn.home) p.turn.opp) = true
        · rw [if_pos hK, List.mem_singleton] at h
          obtain rfl := h
          intro hh
          simp at hh
        · rw [if_neg hK] at h
          exact absurd h (not_mem_nil' m)
      · by_cases hQ : ((p.castleQ p.turn && p.board (sq 0 p.turn.home) == some ⟨p.turn, .rook⟩ &&
          [1, 2, 3].all fun f => empty p.board (sq f p.turn.home)) &&
          !attacked p.board (sq 3 p.turn.home) p.turn.opp) = true
        · rw [if_pos hQ, List.mem_singleton] at h
          obtain rfl := h
          intro hh
          simp at hh
        · rw [if_neg hQ] at h
          exact absurd h (not_mem_nil' m)
    · rw [if_neg hout] at h
      exact absurd h (not_mem_nil' m)

theorem dst_ne_king (p : Pos) (m : Move) (h : m ∈ legalMoves p) (hsafe : inCheck p p.turn.opp = false) :
    ∀ c, p.board m.dst ≠ some ⟨c, .king⟩ := by
  intro c hc
  have hne : c ≠ p.turn := legal_dst_not_own p m h ⟨c, .king⟩ hc
  have hco : c = p.turn.opp := color_eq_opp_of_ne _ _ hne
  subst hco
  have hp := legal_mem_pseudo p m h
  unfold pseudo at hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · rw [List.mem_flatMap] at hp
    obtain ⟨s, _, hm⟩ := hp
    match hb : p.board s with
    | none =>
      rw [hb] at hm
      exact absurd hm (not_mem_nil' m)
    | some q =>
      rw [hb] at hm
      dsimp only at hm
      by_cases hcc : (q.color == p.turn) = true
      · rw [if_pos hcc] at hm
        obtain ⟨h1, -, -⟩ := pieceMove_spec p s q m hm
        have hatt : m.dst ∈ attacks p.board m.src q := by
          rw [h1]
          rcases q with ⟨c0, k0⟩
          cases k0
          · have hmem2 : m ∈ pawnMoves p s c0 := hm
            obtain ⟨-, hdisj, -⟩ := pawnMoves_cases p s c0 m hmem2
            rcases hdisj with hd1 | hd2 | hd3
            · rw [hd1.2.2] at hc
              simp at hc
            · rw [hd2.2.2.2.1] at hc
              simp at hc
            · exact hd3.1
          all_goals
            exact (mem_pieceMoves_nonpawn p s _ m hm (fun he => by simp at he)).2.2
        have hcol : q.color = (p.turn.opp).opp := by
          rw [Color.opp_opp]
          exact beq_iff_eq.mp hcc
        have hck : attacked p.board m.dst (p.turn.opp).opp = true := by
          rw [attacked_iff]
          exact ⟨m.src, q, h1.symm ▸ hb, hcol, hatt⟩
        have hic : inCheck p p.turn.opp = true := (inCheck_iff p p.turn.opp).mpr ⟨m.dst, hc, hck⟩
        rw [hic] at hsafe
        simp at hsafe
      · rw [if_neg hcc] at hm
        exact absurd hm (not_mem_nil' m)
  · obtain ⟨-, -, h3, -⟩ := castleMove_spec p m hp
    rw [h3] at hc
    simp at hc

theorem kingAt_play_nonking (p : Pos) (m : Move) (h : m ∈ legalMoves p) (hk : isKingMove p m = false)
    (hsafe : inCheck p p.turn.opp = false) (c : Color) (s : Sq) :
    kingAt (play p m) c s ↔ kingAt p c s := by
  obtain ⟨q, hq, hcq, hmem⟩ := legal_nonking_mem p m h hk
  have hsd : m.src ≠ m.dst := legal_src_ne_dst p m h
  have hcast : isCastle p m = false := by
    have e : (isKingMove p m && (m.src.file + 2 == m.dst.file || m.dst.file + 2 == m.src.file)) = false := by
      rw [hk]
      rfl
    exact e
  constructor
  · intro hfwd
    unfold kingAt at hfwd
    have hs_dst : s ≠ m.dst := by
      intro h2
      rw [h2, play_board_dst] at hfwd
      cases hpr : m.promo with
      | none =>
        rw [hpr] at hfwd
        rw [kingMove_true_of_board p c m.src hfwd m rfl] at hk
        simp at hk
      | some k =>
        rw [hpr, hq] at hfwd
        have hf2 : (some ⟨q.color, k⟩ : Option Piece) = some ⟨c, .king⟩ := hfwd
        have e : k = .king := congrArg Piece.kind (Option.some.inj hf2)
        subst e
        have hpk := promo_ne_king p m (legal_mem_pseudo p m h)
        rw [hpr] at hpk
        exact absurd rfl hpk
    have hs_src : s ≠ m.src := by
      intro h2
      rw [h2, play_board_src p m hsd] at hfwd
      simp at hfwd
    have hev : epVictim p m ≠ some s := by
      intro heq
      have hbn : (play p m).board s = none := play_board_epVictim p m s heq hs_dst
      rw [hbn] at hfwd
      simp at hfwd
    have hbo := play_board_other p m s hs_src hs_dst hev hcast
    rw [hbo] at hfwd
    exact hfwd
  · intro hbak
    unfold kingAt at hbak
    have hs_src : s ≠ m.src := by
      intro h2
      have hki : isKingMove p m = true := by
        show (p.board m.src).any (·.kind == .king) = true
        rw [← h2, hbak]
        rfl
      rw [hki] at hk
      simp at hk
    have hs_dst : s ≠ m.dst := fun h2 => dst_ne_king p m h hsafe c (h2 ▸ hbak)
    have hev : epVictim p m ≠ some s := by
      intro heq
      obtain ⟨-, -, hvp, -⟩ := epVictim_spec p m s h heq
      have hpi : (⟨p.turn.opp, .pawn⟩ : Piece) = ⟨c, .king⟩ := Option.some.inj (hvp.symm.trans hbak)
      have e : Kind.pawn = Kind.king := congrArg Piece.kind hpi
      exact Kind.noConfusion e
    have hbo := play_board_other p m s hs_src hs_dst hev hcast
    show (play p m).board s = some ⟨c, .king⟩
    rw [hbo]
    exact hbak

theorem legal_not_capture_king (p : Pos) (m : Move) (h : m ∈ legalMoves p) (hsafe : inCheck p p.turn.opp = false) :
    ∀ c, p.board m.dst ≠ some ⟨c, .king⟩ :=
  dst_ne_king p m h hsafe

theorem legal_castleRights_indep (p : Pos) (m : Move) (hk : isKingMove p m = false) (cK cQ : Color → Bool) :
    m ∈ legalMoves p ↔ m ∈ legalMoves { p with castleK := cK, castleQ := cQ } := by
  unfold legalMoves
  rw [List.mem_filter, List.mem_filter]
  constructor
  · intro ⟨hp, hs⟩
    refine ⟨?_, hs⟩
    unfold pseudo at hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · unfold pseudo
      rw [List.mem_append]
      exact Or.inl hp
    · obtain ⟨h1, h2, -, -⟩ := castleMove_spec p m hp
      rw [kingMove_true_of_board p p.turn m.src h2 m rfl] at hk
      simp at hk
  · intro ⟨hp, hs⟩
    refine ⟨?_, hs⟩
    unfold pseudo at hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · unfold pseudo
      rw [List.mem_append]
      exact Or.inl hp
    · obtain ⟨h1, h2, -, -⟩ := castleMove_spec _ m hp
      have h2' : p.board m.src = some ⟨p.turn, .king⟩ := h2
      rw [kingMove_true_of_board p p.turn m.src h2' m rfl] at hk
      simp at hk

end Chess.C364
