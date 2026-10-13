import ChessProof.Spec
import ChessProof.All63.Admissible

namespace Chess.All63

def isCastle (p : Pos) (m : Move) : Bool :=
  (p.board m.src).any (·.kind == .king) && (m.src.file + 2 == m.dst.file || m.dst.file + 2 == m.src.file)

def isEp (p : Pos) (m : Move) : Bool :=
  (p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file && empty p.board m.dst

def isDouble (p : Pos) (m : Move) : Bool :=
  (p.board m.src).any (·.kind == .pawn) && (m.src.rank + 2 == m.dst.rank || m.dst.rank + 2 == m.src.rank)

def moved (p : Pos) (m : Move) : Option Piece :=
  match m.promo with
  | some k => (p.board m.src).map fun q => ⟨q.color, k⟩
  | none => p.board m.src

def epVictim (m : Move) : Sq := sq m.dst.file m.src.rank

def rookFrom (m : Move) : Sq := if m.src.file + 2 == m.dst.file then sq 7 m.src.rank else sq 0 m.src.rank

def rookTo (m : Move) : Sq := if m.src.file + 2 == m.dst.file then sq 5 m.src.rank else sq 3 m.src.rank

theorem play_turn (p : Pos) (m : Move) : (play p m).turn = p.turn.opp := rfl

theorem any_kind_ne (b : Board) (s : Sq) (k1 k2 : Kind) (h : (b s).any (·.kind == k1) = true)
    (h12 : k1 ≠ k2) : (b s).any (·.kind == k2) = false := by
  cases hx : b s with
  | none => rfl
  | some q =>
    have h1 : (q.kind == k1) = true := by rw [hx] at h; exact h
    have hq : q.kind = k1 := of_decide_eq_true h1
    show (q.kind == k2) = false
    rw [hq]; simp [h12]

theorem play_board_simple (p : Pos) (m : Move) (hc : isCastle p m = false) (he : isEp p m = false) (s : Sq) :
    (play p m).board s = if s = m.dst then moved p m else if s = m.src then none else p.board s := by
  have hc1 : ((p.board m.src).any (·.kind == .king) && m.src.file + 2 == m.dst.file) = false := by
    cases hf : (m.src.file + 2 == m.dst.file) <;> simp_all [isCastle]
  have hc2 : ((p.board m.src).any (·.kind == .king) && m.dst.file + 2 == m.src.file) = false := by
    cases hf : (m.dst.file + 2 == m.src.file) <;> simp_all [isCastle]
  unfold play moved
  dsimp only
  unfold isEp at he
  simp [hc1, hc2, he, beq_iff_eq]
  rfl

theorem play_board_ep (p : Pos) (m : Move) (he : isEp p m = true) (s : Sq) :
    (play p m).board s =
      if s = m.dst then moved p m else if s = m.src ∨ s = epVictim m then none else p.board s := by
  unfold isEp at he
  have hK : (p.board m.src).any (·.kind == .king) = false :=
    any_kind_ne _ _ _ _ (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp he).1).1 (by decide)
  have hc1 : ((p.board m.src).any (·.kind == .king) && m.src.file + 2 == m.dst.file) = false := by simp [hK]
  have hc2 : ((p.board m.src).any (·.kind == .king) && m.dst.file + 2 == m.src.file) = false := by simp [hK]
  unfold play moved
  dsimp only
  simp only [hc1, hc2, he]
  simp [beq_iff_eq, epVictim]
  grind

theorem play_board_castle (p : Pos) (m : Move) (hc : isCastle p m = true) (s : Sq) :
    (play p m).board s =
      if s = m.dst then moved p m else if s = m.src then none
      else if s = rookTo m then p.board (rookFrom m) else if s = rookFrom m then none else p.board s := by
  unfold isCastle at hc
  have hK : (p.board m.src).any (·.kind == .king) = true := (Bool.and_eq_true _ _ |>.mp hc).1
  have hf : (m.src.file + 2 == m.dst.file || m.dst.file + 2 == m.src.file) = true :=
    (Bool.and_eq_true _ _ |>.mp hc).2
  have hP : (p.board m.src).any (·.kind == .pawn) = false := any_kind_ne _ _ _ _ hK (by decide)
  have hv : ((p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file && empty p.board m.dst) = false := by
    simp [hP]
  unfold play moved rookFrom rookTo
  dsimp only
  simp only [hv]
  cases hf1 : (m.src.file + 2 == m.dst.file)
  case false =>
    have hf2 : (m.dst.file + 2 == m.src.file) = true := by simp only [hf1, Bool.false_or] at hf; exact hf
    have hc1 : ((p.board m.src).any (·.kind == .king) && m.src.file + 2 == m.dst.file) = false := by simp [hf1]
    have hc2 : ((p.board m.src).any (·.kind == .king) && m.dst.file + 2 == m.src.file) = true := by simp [hK, hf2]
    simp only [hc2]
    simp; grind
  case true =>
    simp [hK]
    grind

theorem play_ep (p : Pos) (m : Move) :
    (play p m).ep = if isDouble p m then some (sq m.src.file ((m.src.rank + m.dst.rank) / 2)) else none := by
  unfold play isDouble
  simp

theorem play_castleK (p : Pos) (m : Move) (c : Color) :
    (play p m).castleK c = (p.castleK c && m.src != sq 4 c.home && m.dst != sq 4 c.home &&
      m.src != sq 7 c.home && m.dst != sq 7 c.home) := by
  unfold play
  simp [Bool.not_or]
  grind

theorem play_castleQ (p : Pos) (m : Move) (c : Color) :
    (play p m).castleQ c = (p.castleQ c && m.src != sq 4 c.home && m.dst != sq 4 c.home &&
      m.src != sq 0 c.home && m.dst != sq 0 c.home) := by
  unfold play
  simp [Bool.not_or]
  grind

theorem mem_legalMoves {p : Pos} {m : Move} (h : m ∈ legalMoves p) :
    m ∈ pseudo p ∧ inCheck (play p m) p.turn = false := by
  unfold legalMoves at h
  rw [List.mem_filter] at h
  exact ⟨h.1, by simpa using h.2⟩

theorem file_lt (s : Sq) : s.file < 8 := Nat.mod_lt _ (by decide)

theorem rank_lt (s : Sq) : s.rank < 8 := by
  have h := s.isLt
  simp only [Sq.rank]
  omega

theorem sq_val (s : Sq) : s.val = s.rank * 8 + s.file := by
  have h := Nat.div_add_mod s.val 8
  simp only [Sq.rank, Sq.file]
  omega

theorem sq_ext {a b : Sq} (hf : a.file = b.file) (hr : a.rank = b.rank) : a = b := by
  have ha := sq_val a
  have hb := sq_val b
  exact Fin.ext (by omega)

theorem sq_file (f r : Nat) (hf : f < 8) (hr : r < 8) : (sq f r).file = f := by
  simp only [sq, Sq.file]
  omega

theorem sq_rank (f r : Nat) (hf : f < 8) (hr : r < 8) : (sq f r).rank = r := by
  simp only [sq, Sq.rank]
  omega

theorem home_lt (c : Color) : c.home < 8 := by cases c <;> decide

theorem opp_opp (c : Color) : c.opp.opp = c := by cases c <;> rfl

theorem board_none_of_empty {b : Board} {t : Sq} (h : empty b t = true) : b t = none := by
  cases hb : b t with
  | none => rfl
  | some q => simp [empty, hb] at h

theorem off_coords {s t : Sq} {df dr : Int} (h : off s df dr = some t) :
    (t.file : Int) = s.file + df ∧ (t.rank : Int) = s.rank + dr := by
  unfold off at h
  dsimp only at h
  split at h
  · rename_i hb
    unfold mkSq at h
    split at h
    · rename_i hb2
      obtain ⟨hf8, hr8⟩ := hb2
      obtain ⟨hf0, hr0⟩ := hb
      have hfI : ((Int.toNat ((s.file : Int) + df) : Nat) : Int) = (s.file : Int) + df :=
        Int.toNat_of_nonneg hf0
      have hrI : ((Int.toNat ((s.rank : Int) + dr) : Nat) : Int) = (s.rank : Int) + dr :=
        Int.toNat_of_nonneg hr0
      injection h with ht
      subst ht
      constructor
      · show ((Int.toNat ((s.rank : Int) + dr) * 8 + Int.toNat ((s.file : Int) + df)) % 8 : Int) =
            (s.file : Int) + df
        omega
      · show ((Int.toNat ((s.rank : Int) + dr) * 8 + Int.toNat ((s.file : Int) + df)) / 8 : Int) =
            (s.rank : Int) + dr
        omega
    · simp at h
  · simp at h

theorem parity_off {s t : Sq} {df dr : Int} (h : off s df dr = some t) (he : (df + dr) % 2 = 0) :
    parity t = parity s := by
  obtain ⟨hf, hr⟩ := off_coords h
  simp only [parity]
  omega

theorem steps_mem {s t : Sq} {ds : List (Int × Int)} (h : t ∈ steps s ds) :
    ∃ d, d ∈ ds ∧ off s d.1 d.2 = some t := by
  simp only [steps, List.mem_filterMap] at h
  obtain ⟨⟨df, dr⟩, hd, hoff⟩ := h
  exact ⟨(df, dr), hd, hoff⟩

theorem ray_parity {b : Board} {s t : Sq} {df dr : Int} (he : (df + dr) % 2 = 0) {n : Nat}
    (h : t ∈ ray b s df dr n) : parity t = parity s := by
  induction n generalizing s with
  | zero => simp [ray] at h
  | succ n ih =>
    have hrw : ray b s df dr (n + 1) = match off s df dr with
      | none => []
      | some u => if empty b u then u :: ray b u df dr n else [u] := rfl
    rw [hrw] at h
    split at h
    · simp at h
    · rename_i u hoff
      by_cases hu : empty b u = true
      · simp only [hu, ite_true, List.mem_cons] at h
        rcases h with htu | hmem
        · subst htu; exact parity_off hoff he
        · rw [ih hmem]; exact parity_off hoff he
      · have huf : empty b u = false := by
          cases h2 : empty b u with
          | false => rfl
          | true => exact absurd h2 hu
        simp [huf] at h
        subst h; exact parity_off hoff he

theorem pseudo_cases {p : Pos} {m : Move} (h : m ∈ pseudo p) :
    (∃ s q, p.board s = some q ∧ q.color = p.turn ∧ m ∈ pieceMoves p s q) ∨ m ∈ castleMoves p := by
  unfold pseudo at h
  rw [List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨s, _, hm⟩ := h
    cases hb : p.board s with
    | none =>
      rw [hb] at hm
      simp at hm
    | some q =>
      rw [hb] at hm
      by_cases hc : (q.color == p.turn) = true
      · simp only [hc, ite_true] at hm
        exact .inl ⟨s, q, hb, beq_iff_eq.mp hc, hm⟩
      · simp only [hc, ite_false] at hm
        simp at hm
  · exact .inr h

theorem pieceMoves_cases {p : Pos} {s : Sq} {q : Piece} {m : Move} (h : m ∈ pieceMoves p s q) :
    (q.kind = .pawn ∧ m ∈ pawnMoves p s q.color) ∨
    (q.kind ≠ .pawn ∧ m.src = s ∧ m.promo = none ∧
      m.dst ∈ (attacks p.board s q).filter fun t => !(p.board t).any (·.color == q.color)) := by
  unfold pieceMoves at h
  split at h
  · rename_i hk
    exact .inl ⟨hk, h⟩
  all_goals (
    rename_i hk
    rw [List.mem_map] at h
    obtain ⟨t, ht, htm⟩ := h
    exact .inr ⟨fun hkp => by rw [hkp] at hk; contradiction, by rw [← htm],
      by rw [← htm], by rw [← htm]; exact ht⟩)

theorem pawnMoves_cases {p : Pos} {s : Sq} {c : Color} {m : Move} (h : m ∈ pawnMoves p s c) :
    (∃ t, off s 0 c.fwd = some t ∧ empty p.board t = true ∧
        (if t.rank == c.last then ∃ k, k ∈ [Kind.knight, .bishop, .rook, .queen] ∧ m = ⟨s, t, some k⟩
         else m = ⟨s, t, none⟩)) ∨
    (∃ t, t ∈ steps s [(1, c.fwd), (-1, c.fwd)] ∧ (foe p.board c t = true ∨ epCap p c t = true) ∧
        (if t.rank == c.last then ∃ k, k ∈ [Kind.knight, .bishop, .rook, .queen] ∧ m = ⟨s, t, some k⟩
         else m = ⟨s, t, none⟩)) ∨
    (∃ t, s.rank = c.pawnHome ∧ (∃ u, off s 0 c.fwd = some u ∧ empty p.board u = true) ∧
        off s 0 (2 * c.fwd) = some t ∧ empty p.board t = true ∧ m = ⟨s, t, none⟩) := by
  unfold pawnMoves at h
  dsimp only at h
  rw [List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨t, ht, hm⟩ := h
    rw [List.mem_append] at ht
    have hmk : (if t.rank == c.last then ∃ k, k ∈ [Kind.knight, .bishop, .rook, .queen] ∧
        m = ⟨s, t, some k⟩ else m = ⟨s, t, none⟩) := by
      by_cases hrl : (t.rank == c.last) = true
      · simp only [hrl, ite_true]
        simp only [hrl, ite_true, List.mem_map] at hm
        obtain ⟨k, hk, hkm⟩ := hm
        exact ⟨k, hk, hkm.symm⟩
      · have hrlf : (t.rank == c.last) = false := by
          cases h2 : (t.rank == c.last) with
          | false => rfl
          | true => exact absurd h2 hrl
        simp [hrlf]
        simp [hrlf] at hm
        exact hm
    rcases ht with ht | ht
    · rw [Option.mem_toList] at ht
      have hf := Option.filter_eq_some_iff.mp ht
      exact .inl ⟨t, hf.1, hf.2, hmk⟩
    · rw [List.mem_filter] at ht
      have hfe : (foe p.board c t || epCap p c t) = true := ht.2
      rw [Bool.or_eq_true] at hfe
      exact .inr (.inl ⟨t, ht.1, hfe, hmk⟩)
  · rw [List.mem_map] at h
    obtain ⟨t, ht, htm⟩ := h
    by_cases hcond : (s.rank == c.pawnHome && ((off s 0 c.fwd).filter (empty p.board)).isSome) = true
    · simp only [hcond, ite_true] at ht
      rw [Option.mem_toList] at ht
      have hf := Option.filter_eq_some_iff.mp ht
      rw [Bool.and_eq_true] at hcond
      have hone : ∃ u, off s 0 c.fwd = some u ∧ empty p.board u = true := by
        have hi : ((off s 0 c.fwd).filter (empty p.board)).isSome = true := hcond.2
        rw [Option.isSome_iff_exists] at hi
        obtain ⟨u, hu⟩ := hi
        exact ⟨u, (Option.filter_eq_some_iff.mp hu).1, (Option.filter_eq_some_iff.mp hu).2⟩
      exact .inr (.inr ⟨t, beq_iff_eq.mp hcond.1, hone, hf.1, hf.2, htm.symm⟩)
    · have hcondf : (s.rank == c.pawnHome && ((off s 0 c.fwd).filter (empty p.board)).isSome) = false := by
        cases h2 : (s.rank == c.pawnHome && ((off s 0 c.fwd).filter (empty p.board)).isSome) with
        | false => rfl
        | true => exact absurd h2 hcond
      simp only [hcondf, ite_false] at ht
      simp at ht

theorem castleMoves_cases {p : Pos} {m : Move} (h : m ∈ castleMoves p) :
    m.src = sq 4 p.turn.home ∧ m.promo = none ∧
    p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ ∧
    attacked p.board (sq 4 p.turn.home) p.turn.opp = false ∧
    ((m.dst = sq 6 p.turn.home ∧ p.castleK p.turn = true ∧
        p.board (sq 7 p.turn.home) = some ⟨p.turn, .rook⟩ ∧
        empty p.board (sq 5 p.turn.home) = true ∧ empty p.board (sq 6 p.turn.home) = true) ∨
     (m.dst = sq 2 p.turn.home ∧ p.castleQ p.turn = true ∧
        p.board (sq 0 p.turn.home) = some ⟨p.turn, .rook⟩ ∧
        empty p.board (sq 1 p.turn.home) = true ∧ empty p.board (sq 2 p.turn.home) = true ∧
        empty p.board (sq 3 p.turn.home) = true)) := by
  unfold castleMoves at h
  dsimp only at h
  split at h
  · rename_i hE
    rw [Bool.and_eq_true, beq_iff_eq] at hE
    obtain ⟨hE1, hE2⟩ := hE
    have hs4 : attacked p.board (sq 4 p.turn.home) p.turn.opp = false := by
      cases h2 : attacked p.board (sq 4 p.turn.home) p.turn.opp with
      | false => rfl
      | true => simp [h2] at hE2
    rw [List.mem_append] at h
    rcases h with hK | hQ
    · split at hK
      · rename_i hcond
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcond
        obtain ⟨⟨⟨hcK, hr7⟩, hfree⟩, _⟩ := hcond
        rw [beq_iff_eq] at hr7
        have h5 : empty p.board (sq 5 p.turn.home) = true := List.all_eq_true.mp hfree 5 (by simp)
        have h6 : empty p.board (sq 6 p.turn.home) = true := List.all_eq_true.mp hfree 6 (by simp)
        have hm : m = ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ := List.mem_singleton.mp hK
        subst hm
        exact ⟨rfl, rfl, hE1, hs4, .inl ⟨rfl, hcK, hr7, h5, h6⟩⟩
      · simp at hK
    · split at hQ
      · rename_i hcond
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcond
        obtain ⟨⟨⟨hcQ, hr0⟩, hfree⟩, _⟩ := hcond
        rw [beq_iff_eq] at hr0
        have h1 : empty p.board (sq 1 p.turn.home) = true := List.all_eq_true.mp hfree 1 (by simp)
        have h2 : empty p.board (sq 2 p.turn.home) = true := List.all_eq_true.mp hfree 2 (by simp)
        have h3 : empty p.board (sq 3 p.turn.home) = true := List.all_eq_true.mp hfree 3 (by simp)
        have hm : m = ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ := List.mem_singleton.mp hQ
        subst hm
        exact ⟨rfl, rfl, hE1, hs4, .inr ⟨rfl, hcQ, hr0, h1, h2, h3⟩⟩
      · simp at hQ
  · simp at h

theorem attacked_of_mem {b : Board} {s : Sq} {q : Piece} {c : Color} (hs : b s = some q)
    (hc : q.color = c) {t : Sq} (ht : t ∈ attacks b s q) : attacked b t c = true := by
  rw [attacked, List.any_eq_true]
  refine ⟨s, List.mem_finRange s, ?_⟩
  rw [hs, Bool.and_eq_true]
  exact ⟨beq_iff_eq.mpr hc, List.contains_iff_mem.mpr ht⟩

theorem move_src_of_pieceMoves {p : Pos} {s : Sq} {q : Piece} {m : Move} (h : m ∈ pieceMoves p s q) :
    m.src = s := by
  rcases pieceMoves_cases h with ⟨_, hpm⟩ | ⟨_, hs, _, _⟩
  · rcases pawnMoves_cases hpm with ⟨t, _, _, hmk⟩ | ⟨t, _, _, hmk⟩ | ⟨t, _, _, _, _, hm⟩
    · split at hmk
      · obtain ⟨_, _, hm⟩ := hmk
        rw [hm]
      · rw [hmk]
    · split at hmk
      · obtain ⟨_, _, hm⟩ := hmk
        rw [hm]
      · rw [hmk]
    · rw [hm]
  · exact hs

theorem pseudo_src {p : Pos} {m : Move} (h : m ∈ pseudo p) :
    ∃ q, p.board m.src = some q ∧ q.color = p.turn := by
  rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hc
  · have hsrc := move_src_of_pieceMoves hpm
    exact ⟨q, by rw [hsrc]; exact hbs, hcol⟩
  · obtain ⟨hsrc, _, hb, _, _⟩ := castleMoves_cases hc
    exact ⟨⟨p.turn, .king⟩, by rw [hsrc]; exact hb, rfl⟩

theorem pseudo_dst {p : Pos} {m : Move} (h : m ∈ pseudo p) :
    ∀ q, p.board m.dst = some q → q.color ≠ p.turn := by
  intro q' hdq
  rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hc
  · rcases pieceMoves_cases hpm with ⟨hkp, hpw⟩ | ⟨_, hsrc, _, hdt⟩
    · rcases pawnMoves_cases hpw with ⟨t, _, he, hmk⟩ | ⟨t, hst, hfe, hmk⟩ | ⟨t, _, _, _, he, hm⟩
      · have hdst : m.dst = t := by
          split at hmk
          · obtain ⟨_, _, hm⟩ := hmk; rw [hm]
          · rw [hmk]
        rw [hdst] at hdq
        exact absurd hdq (by rw [board_none_of_empty he]; simp)
      · have hdst : m.dst = t := by
          split at hmk
          · obtain ⟨_, _, hm⟩ := hmk; rw [hm]
          · rw [hmk]
        rw [hdst] at hdq
        rcases hfe with hfoe | hep
        · unfold foe at hfoe
          rw [hdq] at hfoe
          simp at hfoe
          rw [← hcol]
          exact hfoe
        · unfold epCap at hep
          rw [Bool.and_eq_true, Bool.and_eq_true] at hep
          have := board_none_of_empty hep.1.2
          rw [this] at hdq
          simp at hdq
      · rw [hm] at hdq
        exact absurd hdq (by rw [board_none_of_empty he]; simp)
    · rw [List.mem_filter] at hdt
      have hfilt := hdt.2
      intro hqcol
      rw [hdq] at hfilt
      have hthis : (q'.color == q.color) = true := beq_iff_eq.mpr (by rw [hqcol, hcol])
      simp [Option.any_some, hthis] at hfilt
  · obtain ⟨_, _, _, _, hside⟩ := castleMoves_cases hc
    rcases hside with ⟨hdst, _, _, _, h6⟩ | ⟨hdst, _, _, _, h2, _⟩
    · rw [hdst] at hdq
      exact absurd hdq (by rw [board_none_of_empty h6]; simp)
    · rw [hdst] at hdq
      exact absurd hdq (by rw [board_none_of_empty h2]; simp)

theorem move_eq {m : Move} {s t : Sq} {pr : Option Kind} (h : m = ⟨s, t, pr⟩) :
    m.src = s ∧ m.dst = t ∧ m.promo = pr := by
  subst h
  exact ⟨rfl, rfl, rfl⟩

theorem pseudo_promo {p : Pos} {m : Move} (h : m ∈ pseudo p) (k : Kind) (hk : m.promo = some k) :
    p.board m.src = some ⟨p.turn, .pawn⟩ ∧ m.dst.rank = p.turn.last ∧ k ≠ .pawn ∧ k ≠ .king := by
  rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hcm
  · obtain ⟨qc, qk⟩ := q
    subst hcol
    rcases pieceMoves_cases hpm with ⟨hkp, hpw⟩ | ⟨_, _, hpn, _⟩
    · rcases pawnMoves_cases hpw with ⟨t, _, _, hmk⟩ | ⟨t, _, _, hmk⟩ | ⟨t, _, _, _, _, hm⟩
      · by_cases hrl : (t.rank == p.turn.last) = true
        · simp only [hrl, ite_true] at hmk
          obtain ⟨k', hkl, hm⟩ := hmk
          obtain ⟨hms, hmd, hmp⟩ := move_eq hm
          rw [hmp] at hk
          have hkk : k' = k := by injection hk
          subst hkk
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hms, hbs]
            have hkp' : qk = .pawn := hkp
            subst hkp'
            rfl
          · rw [hmd]
            exact beq_iff_eq.mp hrl
          · simp at hkl
            rcases hkl with h | h | h | h <;> subst h <;> decide
          · simp at hkl
            rcases hkl with h | h | h | h <;> subst h <;> decide
        · simp only [hrl, ite_false] at hmk
          obtain ⟨_, _, hmp⟩ := move_eq hmk
          rw [hmp] at hk
          simp at hk
      · by_cases hrl : (t.rank == p.turn.last) = true
        · simp only [hrl, ite_true] at hmk
          obtain ⟨k', hkl, hm⟩ := hmk
          obtain ⟨hms, hmd, hmp⟩ := move_eq hm
          rw [hmp] at hk
          have hkk : k' = k := by injection hk
          subst hkk
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hms, hbs]
            have hkp' : qk = .pawn := hkp
            subst hkp'
            rfl
          · rw [hmd]
            exact beq_iff_eq.mp hrl
          · simp at hkl
            rcases hkl with h | h | h | h <;> subst h <;> decide
          · simp at hkl
            rcases hkl with h | h | h | h <;> subst h <;> decide
        · simp only [hrl, ite_false] at hmk
          obtain ⟨_, _, hmp⟩ := move_eq hmk
          rw [hmp] at hk
          simp at hk
      · obtain ⟨_, _, hmp⟩ := move_eq hm
        rw [hmp] at hk
        simp at hk
    · rw [hpn] at hk
      simp at hk
  · obtain ⟨_, hpn, _, _, _⟩ := castleMoves_cases hcm
    rw [hpn] at hk
    simp at hk

theorem color_cases (c : Color) :
    (c = .white ∧ c.fwd = 1 ∧ c.pawnHome = 1 ∧ c.last = 7 ∧ c.home = 0 ∧ c.opp = .black) ∨
    (c = .black ∧ c.fwd = -1 ∧ c.pawnHome = 6 ∧ c.last = 0 ∧ c.home = 7 ∧ c.opp = .white) := by
  cases c
  · exact .inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact .inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pseudo_pawn_last {p : Pos} {m : Move} (h : m ∈ pseudo p) (hp : p.board m.src = some ⟨p.turn, .pawn⟩)
    (hr : m.dst.rank = p.turn.last) : m.promo.isSome := by
  rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hcm
  · have hsrc := move_src_of_pieceMoves hpm
    rw [hsrc] at hp
    have hsq : q = ⟨p.turn, .pawn⟩ := by
      rw [hp] at hbs
      injection hbs with hh
      exact hh.symm
    subst hsq
    rcases pieceMoves_cases hpm with ⟨_, hpw⟩ | ⟨hknp, _, _, _⟩
    · rcases pawnMoves_cases hpw with ⟨t, _, _, hmk⟩ | ⟨t, _, _, hmk⟩ |
        ⟨t, hsr, ⟨u, hof1, _⟩, hof2, _, hm⟩
      · split at hmk
        · obtain ⟨k', _, hm⟩ := hmk
          obtain ⟨_, _, hmp⟩ := move_eq hm
          rw [hmp]
          rfl
        · rename_i hrlf
          obtain ⟨hms, hmd, hmp⟩ := move_eq hmk
          rw [hmd] at hr
          simp at hrlf
          exact absurd hr hrlf
      · split at hmk
        · obtain ⟨k', _, hm⟩ := hmk
          obtain ⟨_, _, hmp⟩ := move_eq hm
          rw [hmp]
          rfl
        · rename_i hrlf
          obtain ⟨hms, hmd, hmp⟩ := move_eq hmk
          rw [hmd] at hr
          simp at hrlf
          exact absurd hr hrlf
      · obtain ⟨hms, hmd, hmp⟩ := move_eq hm
        rw [hmd] at hr
        have hc2 := (off_coords hof2).2
        rcases color_cases p.turn with ⟨_, hfd, hph, hl, _, _⟩ | ⟨_, hfd, hph, hl, _, _⟩
        · rw [hph] at hsr
          rw [hfd] at hc2
          rw [hl] at hr
          omega
        · rw [hph] at hsr
          rw [hfd] at hc2
          rw [hl] at hr
          omega
    · exact absurd rfl hknp
  · obtain ⟨hsrc, _, hb, _, _⟩ := castleMoves_cases hcm
    rw [hsrc, hb] at hp
    simp at hp

theorem pseudo_pawn_rank {p : Pos} {m : Move} (h : m ∈ pseudo p) (hp : p.board m.src = some ⟨p.turn, .pawn⟩) :
    (m.dst.rank : Int) = m.src.rank + p.turn.fwd ∨
      (m.src.rank = p.turn.pawnHome ∧ (m.dst.rank : Int) = m.src.rank + 2 * p.turn.fwd ∧ m.dst.file = m.src.file) := by
  rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hcm
  · have hsrc := move_src_of_pieceMoves hpm
    rw [hsrc] at hp
    have hsq : q = ⟨p.turn, .pawn⟩ := by
      rw [hp] at hbs
      injection hbs with hh
      exact hh.symm
    subst hsq
    rcases pieceMoves_cases hpm with ⟨_, hpw⟩ | ⟨hknp, _, _, _⟩
    · rcases pawnMoves_cases hpw with ⟨t, hof, _, hmk⟩ | ⟨t, hst, _, hmk⟩ |
        ⟨t, hsr, _, hof2, _, hm⟩
      · left
        have hdst : m.dst = t := by
          split at hmk
          · obtain ⟨_, _, hm⟩ := hmk; rw [hm]
          · rw [hmk]
        rw [hsrc, hdst]
        exact (off_coords hof).2
      · left
        have hdst : m.dst = t := by
          split at hmk
          · obtain ⟨_, _, hm⟩ := hmk; rw [hm]
          · rw [hmk]
        obtain ⟨d, hd, hoff⟩ := steps_mem hst
        simp at hd
        rcases hd with rfl | rfl
        all_goals (
          rw [hsrc, hdst]
          exact (off_coords hoff).2)
      · obtain ⟨hms, hmd, _⟩ := move_eq hm
        right
        refine ⟨?_, ?_, ?_⟩
        · rw [hms]; exact hsr
        · rw [hms, hmd]; exact (off_coords hof2).2
        · have hf := (off_coords hof2).1
          rw [hms, hmd]
          omega
    · exact absurd rfl hknp
  · obtain ⟨hsrc, _, hb, _, _⟩ := castleMoves_cases hcm
    rw [hsrc, hb] at hp
    simp at hp

theorem pseudo_bishop_parity {p : Pos} {m : Move} (h : m ∈ pseudo p)
    (hb : p.board m.src = some ⟨p.turn, .bishop⟩) : parity m.dst = parity m.src := by
  rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hcm
  · have hsrc := move_src_of_pieceMoves hpm
    rw [hsrc] at hb
    have hsq : q = ⟨p.turn, .bishop⟩ := by
      rw [hb] at hbs
      injection hbs with hh
      exact hh.symm
    subst hsq
    rcases pieceMoves_cases hpm with ⟨hkp, _⟩ | ⟨_, _, _, hdt⟩
    · simp at hkp
    · rw [List.mem_filter] at hdt
      have hatt : m.dst ∈ rays p.board s bishopD := hdt.1
      unfold rays at hatt
      rw [List.mem_flatMap] at hatt
      obtain ⟨d, hd, hr⟩ := hatt
      rw [hsrc] at *
      simp [bishopD] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact ray_parity (by decide) hr
      · exact ray_parity (by decide) hr
      · exact ray_parity (by decide) hr
      · exact ray_parity (by decide) hr
  · obtain ⟨hsrc, _, hb2, _, _⟩ := castleMoves_cases hcm
    rw [hsrc, hb2] at hb
    simp at hb

theorem pseudo_castle {p : Pos} {m : Move} (h : m ∈ pseudo p) (hc : isCastle p m = true) :
    m.promo = none ∧ m.src = sq 4 p.turn.home ∧ p.board m.src = some ⟨p.turn, .king⟩ ∧ p.board m.dst = none ∧
      p.board (rookTo m) = none ∧ p.board (rookFrom m) = some ⟨p.turn, .rook⟩ ∧
      ((m.dst = sq 6 p.turn.home ∧ p.castleK p.turn = true) ∨
       (m.dst = sq 2 p.turn.home ∧ p.castleQ p.turn = true)) := by
  unfold isCastle at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hk, hdf⟩ := hc
  have hcm : m ∈ castleMoves p := by
    rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hcm
    · have hsrc0 := move_src_of_pieceMoves hpm
      rw [hsrc0, hbs] at hk
      simp only [Option.any_some] at hk
      have hqk : q.kind = .king := beq_iff_eq.mp hk
      obtain ⟨qc, qk⟩ := q
      have hkk : qk = .king := hqk
      subst hkk
      rcases pieceMoves_cases hpm with ⟨hkp, hpw⟩ | ⟨hknp, hsrc, _, hdt⟩
      · simp at hkp
      · rw [List.mem_filter] at hdt
        have hatt : m.dst ∈ steps s queenD := hdt.1
        obtain ⟨d, hd, hoff⟩ := steps_mem hatt
        simp [queenD, rookD, bishopD] at hd
        rw [Bool.or_eq_true] at hdf
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (rcases hdf with h1 | h1 <;>
            (rw [beq_iff_eq] at h1
             rw [hsrc] at h1
             have cf := (off_coords hoff).1
             dsimp only at cf
             omega))
    · exact hcm
  obtain ⟨hsrc, hpn, hbK, _, hside⟩ := castleMoves_cases hcm
  rcases hside with ⟨hdst, hck, hr7, h5, h6⟩ | ⟨hdst, hcq, hr0, h1e, h2e, h3e⟩
  · have hrf : rookFrom m = sq 7 p.turn.home := by
      have g1 := sq_file 4 p.turn.home (by decide) (home_lt _)
      have g2 := sq_file 6 p.turn.home (by decide) (home_lt _)
      have g3 := sq_rank 4 p.turn.home (by decide) (home_lt _)
      unfold rookFrom
      rw [hsrc, hdst, g1, g2, g3]
      rfl
    have hrt : rookTo m = sq 5 p.turn.home := by
      have g1 := sq_file 4 p.turn.home (by decide) (home_lt _)
      have g2 := sq_file 6 p.turn.home (by decide) (home_lt _)
      have g3 := sq_rank 4 p.turn.home (by decide) (home_lt _)
      unfold rookTo
      rw [hsrc, hdst, g1, g2, g3]
      rfl
    exact ⟨hpn, hsrc, by rw [hsrc]; exact hbK, by rw [hdst]; exact board_none_of_empty h6,
      by rw [hrt]; exact board_none_of_empty h5, by rw [hrf]; exact hr7, .inl ⟨hdst, hck⟩⟩
  · have hrf : rookFrom m = sq 0 p.turn.home := by
      have g1 := sq_file 4 p.turn.home (by decide) (home_lt _)
      have g2 := sq_file 2 p.turn.home (by decide) (home_lt _)
      have g3 := sq_rank 4 p.turn.home (by decide) (home_lt _)
      unfold rookFrom
      rw [hsrc, hdst, g1, g2, g3]
      rfl
    have hrt : rookTo m = sq 3 p.turn.home := by
      have g1 := sq_file 4 p.turn.home (by decide) (home_lt _)
      have g2 := sq_file 2 p.turn.home (by decide) (home_lt _)
      have g3 := sq_rank 4 p.turn.home (by decide) (home_lt _)
      unfold rookTo
      rw [hsrc, hdst, g1, g2, g3]
      rfl
    exact ⟨hpn, hsrc, by rw [hsrc]; exact hbK, by rw [hdst]; exact board_none_of_empty h2e,
      by rw [hrt]; exact board_none_of_empty h3e, by rw [hrf]; exact hr0, .inr ⟨hdst, hcq⟩⟩

theorem pseudo_ep {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ pseudo p) (he : isEp p m = true) :
    p.ep = some m.dst ∧ p.board (epVictim m) = some ⟨p.turn.opp, .pawn⟩ ∧ m.promo = none ∧
      (m.dst.rank : Int) = m.src.rank + p.turn.fwd := by
  unfold isEp at he
  rw [Bool.and_eq_true, Bool.and_eq_true] at he
  obtain ⟨⟨hkP, hfd⟩, hempty⟩ := he
  rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hcm
  · have hsrc := move_src_of_pieceMoves hpm
    rw [hsrc, hbs] at hkP
    simp only [Option.any_some] at hkP
    obtain ⟨qc, qk⟩ := q
    have hk' : qk = .pawn := beq_iff_eq.mp hkP
    subst hk'
    have hcol' : qc = p.turn := hcol
    rcases pieceMoves_cases hpm with ⟨_, hpw⟩ | ⟨hknp, _, _, _⟩
    · have hpw' : m ∈ pawnMoves p s qc := hpw
      rcases pawnMoves_cases hpw' with ⟨t, hof, _, hmk⟩ | ⟨t, hst, hfe, hmk⟩ |
          ⟨t, hsr, _, hof2, _, hm⟩
      · have hdst : m.dst = t := by
          split at hmk
          · obtain ⟨_, _, hm⟩ := hmk; rw [hm]
          · rw [hmk]
        have cf : (t.file : Int) = (s.file : Int) + (0 : Int) := (off_coords hof).1
        rw [hsrc, hdst] at hfd
        rw [bne_iff_ne] at hfd
        exact absurd (by omega : s.file = t.file) hfd
      · have hdst : m.dst = t := by
          split at hmk
          · obtain ⟨_, _, hm⟩ := hmk; rw [hm]
          · rw [hmk]
        rcases hfe with hfoe | hep
        · have hbnone : p.board t = none := by
            rw [hdst] at hempty
            exact board_none_of_empty hempty
          unfold foe at hfoe
          rw [hbnone] at hfoe
          simp at hfoe
        · unfold epCap at hep
          rw [Bool.and_eq_true, Bool.and_eq_true] at hep
          obtain ⟨⟨hep1, _⟩, hmatch⟩ := hep
          have hep' : p.ep = some t := beq_iff_eq.mp hep1
          revert hmatch
          cases hoff : off t 0 (-qc.fwd) with
          | none =>
            intro hmatch
            simp at hmatch
          | some u =>
            intro hmatch
            have hu : p.board u = some ⟨qc.opp, .pawn⟩ := beq_iff_eq.mp hmatch
            have cf : (u.file : Int) = (t.file : Int) + (0 : Int) := (off_coords hoff).1
            have cu : (u.rank : Int) = (t.rank : Int) + -qc.fwd := (off_coords hoff).2
            obtain ⟨d, hd2, hoff2⟩ := steps_mem hst
            simp at hd2
            rcases hd2 with rfl | rfl
            all_goals (
              have cr : (t.rank : Int) = (s.rank : Int) + qc.fwd := (off_coords hoff2).2
              have hEV : epVictim m = sq t.file s.rank := by
                unfold epVictim
                rw [hdst, hsrc]
              have hEVu : epVictim m = u := by
                rw [hEV]
                apply sq_ext
                · rw [sq_file _ _ (file_lt t) (rank_lt s)]
                  omega
                · rw [sq_rank _ _ (file_lt t) (rank_lt s)]
                  rcases color_cases qc with ⟨_, hfw, _, _, _, _⟩ | ⟨_, hfw, _, _, _, _⟩
                  · rw [hfw] at cr cu
                    omega
                  · rw [hfw] at cr cu
                    omega
              have hEp : EpOk p t := hA.ep t hep'
              have htne : t.rank ≠ qc.last := by
                rcases color_cases qc with ⟨hqcw, _, _, hl, _, _⟩ | ⟨hqcb, _, _, hl, _, _⟩
                · rw [hl]
                  have hEp' := hEp
                  unfold EpOk at hEp'
                  rw [hcol'.symm.trans hqcw] at hEp'
                  dsimp only at hEp'
                  obtain ⟨hr5, _⟩ := hEp'
                  omega
                · rw [hl]
                  have hEp' := hEp
                  unfold EpOk at hEp'
                  rw [hcol'.symm.trans hqcb] at hEp'
                  dsimp only at hEp'
                  obtain ⟨hr2, _⟩ := hEp'
                  omega
              cases hbeq : (t.rank == qc.last) with
              | true => exact absurd (beq_iff_eq.mp hbeq) htne
              | false =>
                simp [hbeq] at hmk
                obtain ⟨_, _, hmp⟩ := move_eq hmk
                refine ⟨by rw [hdst]; exact hep', ?_, hmp, ?_⟩
                · rw [hEVu]
                  exact hcol' ▸ hu
                · rw [hsrc, hdst]
                  exact hcol' ▸ cr)
      · have hdst : m.dst = t := by
          obtain ⟨_, hmd, _⟩ := move_eq hm
          exact hmd
        have cf : (t.file : Int) = (s.file : Int) + (0 : Int) := (off_coords hof2).1
        rw [hsrc, hdst] at hfd
        rw [bne_iff_ne] at hfd
        exact absurd (by omega : s.file = t.file) hfd
    · exact absurd (by rfl : (⟨qc, Kind.pawn⟩ : Piece).kind = .pawn) hknp
  · obtain ⟨hsrc2, _, hb, _, _⟩ := castleMoves_cases hcm
    rw [hsrc2, hb] at hkP
    simp [Option.any_some] at hkP

theorem pseudo_double {p : Pos} {m : Move} (h : m ∈ pseudo p) (hd : isDouble p m = true) :
    m.src.rank = p.turn.pawnHome ∧ m.dst.file = m.src.file ∧ (m.dst.rank : Int) = m.src.rank + 2 * p.turn.fwd ∧
      p.board m.dst = none ∧ p.board (sq m.src.file ((m.src.rank + m.dst.rank) / 2)) = none := by
  unfold isDouble at hd
  rw [Bool.and_eq_true] at hd
  obtain ⟨hkP, hdr⟩ := hd
  rw [Bool.or_eq_true] at hdr
  rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hcm
  · have hsrc := move_src_of_pieceMoves hpm
    rw [hsrc, hbs] at hkP
    simp only [Option.any_some] at hkP
    obtain ⟨qc, qk⟩ := q
    have hk' : qk = .pawn := beq_iff_eq.mp hkP
    subst hk'
    rcases pieceMoves_cases hpm with ⟨_, hpw⟩ | ⟨hknp, _, _, _⟩
    · rcases pawnMoves_cases hpw with ⟨t, hof, _, hmk⟩ | ⟨t, hst, _, hmk⟩ |
        ⟨t, hsr, ⟨u, hof1, he1⟩, hof2, he2, hm⟩
      · have hdst : m.dst = t := by
          split at hmk
          · obtain ⟨_, _, hm⟩ := hmk; rw [hm]
          · rw [hmk]
        have cr := (off_coords hof).2
        rcases hdr with h1 | h1 <;>
          (rw [beq_iff_eq] at h1
           rw [hsrc, hdst] at h1
           rcases color_cases qc with ⟨_, hfd, _, _, _, _⟩ | ⟨_, hfd, _, _, _, _⟩
           · rw [hfd] at cr
             omega
           · rw [hfd] at cr
             omega)
      · have hdst : m.dst = t := by
          split at hmk
          · obtain ⟨_, _, hm⟩ := hmk; rw [hm]
          · rw [hmk]
        obtain ⟨d, hd2, hoff⟩ := steps_mem hst
        simp at hd2
        rcases hd2 with rfl | rfl
        all_goals (
          have cr : (t.rank : Int) = s.rank + qc.fwd := (off_coords hoff).2
          rcases hdr with h1 | h1 <;>
            (rw [beq_iff_eq] at h1
             rw [hsrc, hdst] at h1
             rcases color_cases qc with ⟨_, hfd, _, _, _, _⟩ | ⟨_, hfd, _, _, _, _⟩
             · rw [hfd] at cr
               omega
             · rw [hfd] at cr
               omega))
      · obtain ⟨hms, hmd, _⟩ := move_eq hm
        have cr1 : (u.rank : Int) = (s.rank : Int) + qc.fwd := (off_coords hof1).2
        have cf1 : (u.file : Int) = (s.file : Int) + (0 : Int) := (off_coords hof1).1
        have cr2 := (off_coords hof2).2
        have cf2 := (off_coords hof2).1
        have hbl : (s.rank + t.rank) / 2 < 8 := by
          have hs8 := rank_lt s
          have ht8 := rank_lt t
          omega
        have hmid : sq s.file ((s.rank + t.rank) / 2) = u := by
          apply sq_ext
          · rw [sq_file _ _ (file_lt s) hbl]
            omega
          · rw [sq_rank _ _ (file_lt s) hbl]
            rcases color_cases qc with ⟨_, hfd, _, _, _, _⟩ | ⟨_, hfd, _, _, _, _⟩
            · rw [hfd] at cr1 cr2
              omega
            · rw [hfd] at cr1 cr2
              omega
        rw [hms, hmd]
        have hcol' : qc = p.turn := hcol
        have e0 : s.rank = qc.pawnHome := hsr
        refine ⟨hcol' ▸ e0, by omega, ?_, by exact board_none_of_empty he2, ?_⟩
        · have cr2' : (t.rank : Int) = (s.rank : Int) + 2 * qc.fwd := cr2
          exact hcol' ▸ cr2'
        · rw [hmid]
          exact board_none_of_empty he1
    · exact absurd (by rfl : (⟨qc, Kind.pawn⟩ : Piece).kind = .pawn) hknp
  · obtain ⟨hsrc2, _, hb, _, _⟩ := castleMoves_cases hcm
    rw [hsrc2, hb] at hkP
    simp [Option.any_some] at hkP

theorem pseudo_no_king_capture {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ pseudo p) :
    p.board m.dst ≠ some ⟨p.turn.opp, .king⟩ := by
  intro hkc
  have hatt : attacked p.board m.dst p.turn = true := by
    rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hcm
    · rcases pieceMoves_cases hpm with ⟨hkp, hpw⟩ | ⟨_, _, _, hdt⟩
      · obtain ⟨qc, qk⟩ := q
        have hk' : qk = .pawn := hkp
        subst hk'
        have hpw' : m ∈ pawnMoves p s qc := hpw
        rcases pawnMoves_cases hpw' with ⟨t, _, he, hmk⟩ | ⟨t, hst, _, hmk⟩ | ⟨t, _, _, _, he2, hm⟩
        · have hdst : m.dst = t := by
            split at hmk
            · obtain ⟨_, _, hm⟩ := hmk; rw [hm]
            · rw [hmk]
          rw [hdst] at hkc
          exact absurd hkc (by rw [board_none_of_empty he]; simp)
        · have hdst : m.dst = t := by
            split at hmk
            · obtain ⟨_, _, hm⟩ := hmk; rw [hm]
            · rw [hmk]
          have hmem : m.dst ∈ attacks p.board s ⟨qc, .pawn⟩ := by
            rw [hdst]
            exact hst
          exact attacked_of_mem hbs hcol hmem
        · obtain ⟨_, hmd, _⟩ := move_eq hm
          rw [hmd] at hkc
          exact absurd hkc (by rw [board_none_of_empty he2]; simp)
      · exact attacked_of_mem hbs hcol (List.mem_filter.mp hdt).1
    · obtain ⟨_, _, _, _, hside⟩ := castleMoves_cases hcm
      rcases hside with ⟨hdst, _, _, _, h6⟩ | ⟨hdst, _, _, _, h2, _⟩
      · rw [hdst] at hkc
        exact absurd hkc (by rw [board_none_of_empty h6]; simp)
      · rw [hdst] at hkc
        exact absurd hkc (by rw [board_none_of_empty h2]; simp)
  obtain ⟨hbk, huniq⟩ := kingSq_spec p p.turn.opp (hA.kings _)
  have hks : m.dst = kingSq p p.turn.opp := huniq m.dst hkc
  have hIC : inCheck p p.turn.opp = true := by
    rw [inCheck_iff_attacked p _ (hA.kings _), ← hks, opp_opp p.turn]
    exact hatt
  have hs := hA.safe
  rw [hIC] at hs
  simp at hs

def bupd (b : Board) (x : Sq) (v : Option Piece) : Board := fun s => if s = x then v else b s

theorem bupd_self (b : Board) (x : Sq) (v : Option Piece) : bupd b x v x = v := by
  simp [bupd]

theorem bupd_ne (b : Board) {x y : Sq} (h : y ≠ x) (v : Option Piece) : bupd b x v y = b y := by
  simp [bupd, h]

theorem sq_ne_of_file_ne {f₁ r₁ f₂ r₂ : Nat} (hf₁ : f₁ < 8) (hr₁ : r₁ < 8)
    (hf₂ : f₂ < 8) (hr₂ : r₂ < 8) (hff : f₁ ≠ f₂) : sq f₁ r₁ ≠ sq f₂ r₂ := by
  intro he
  have h1 := congrArg Sq.file he
  rw [sq_file f₁ r₁ hf₁ hr₁, sq_file f₂ r₂ hf₂ hr₂] at h1
  exact hff h1

theorem mkSq_sq (s : Sq) : mkSq s.file s.rank = some s := by
  unfold mkSq
  split
  · rename_i h
    exact congrArg some (Fin.ext (sq_val s).symm)
  · rename_i h
    exact absurd ⟨file_lt s, rank_lt s⟩ h

theorem off_int {a t : Sq} {df dr : Int}
    (hf : (t.file : Int) = a.file + df) (hr : (t.rank : Int) = a.rank + dr) :
    off a df dr = some t := by
  unfold off
  dsimp only
  rw [if_pos ⟨by omega, by omega⟩]
  have e1 : Int.toNat ((a.file : Int) + df) = t.file := by
    have c1 := Int.toNat_of_nonneg (by omega : (0 : Int) ≤ (a.file : Int) + df)
    omega
  have e2 : Int.toNat ((a.rank : Int) + dr) = t.rank := by
    have c2 := Int.toNat_of_nonneg (by omega : (0 : Int) ≤ (a.rank : Int) + dr)
    omega
  rw [e1, e2]
  exact mkSq_sq t

theorem ray_slant {b : Board} {s t : Sq} {df dr : Int} {n : Nat} (h : t ∈ ray b s df dr n) :
    (0 < df → (s.file : Int) < t.file) ∧ (df < 0 → (t.file : Int) < s.file) ∧
    (df = 0 → (t.file : Int) = s.file) ∧
    (0 < dr → (s.rank : Int) < t.rank) ∧ (dr < 0 → (t.rank : Int) < s.rank) ∧
    (dr = 0 → (t.rank : Int) = s.rank) := by
  induction n generalizing s with
  | zero => simp [ray] at h
  | succ n ih =>
    have hrw : ray b s df dr (n + 1) = match off s df dr with
      | none => []
      | some u => if empty b u then u :: ray b u df dr n else [u] := rfl
    rw [hrw] at h
    split at h
    · simp at h
    · rename_i u hoff
      obtain ⟨hfu, hru⟩ := off_coords hoff
      by_cases huu : empty b u = true
      · simp only [huu, ite_true, List.mem_cons] at h
        rcases h with htu | hmem
        · subst htu
          exact ⟨fun hd => by omega, fun hd => by omega, fun hd => by omega,
            fun hd => by omega, fun hd => by omega, fun hd => by omega⟩
        · obtain ⟨g1, g2, g3, g4, g5, g6⟩ := ih hmem
          exact ⟨fun hd => by have g := g1 hd; omega, fun hd => by have g := g2 hd; omega,
            fun hd => by have g := g3 hd; omega, fun hd => by have g := g4 hd; omega,
            fun hd => by have g := g5 hd; omega, fun hd => by have g := g6 hd; omega⟩
      · have huf : empty b u = false := by
          cases h2 : empty b u with
          | false => rfl
          | true => exact absurd h2 huu
        simp [huf] at h
        subst h
        exact ⟨fun hd => by omega, fun hd => by omega, fun hd => by omega,
          fun hd => by omega, fun hd => by omega, fun hd => by omega⟩

theorem dir_ne_of_mem {d : Int × Int} (hd : d ∈ knightD ∨ d ∈ bishopD ∨ d ∈ rookD ∨ d ∈ queenD) :
    d.1 ≠ 0 ∨ d.2 ≠ 0 := by
  rcases hd with hd | hd | hd | hd
  · simp [knightD] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact .inl (by decide)
  · simp [bishopD] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact .inl (by decide)
  · simp [rookD] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      first | exact .inl (by decide) | exact .inr (by decide)
  · simp [queenD, rookD, bishopD] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact .inl (by decide) | exact .inr (by decide)

theorem steps_ne {s t : Sq} {L : List (Int × Int)} (h : t ∈ steps s L)
    (hd : ∀ d ∈ L, d.1 ≠ 0 ∨ d.2 ≠ 0) : t ≠ s := by
  obtain ⟨⟨df, dr⟩, hdm, hoff⟩ := steps_mem h
  obtain ⟨hf, hr⟩ := off_coords hoff
  rcases hd (df, dr) hdm with h1 | h2
  · exact fun he => by subst he; omega
  · exact fun he => by subst he; omega

theorem rays_ne {b : Board} {s t : Sq} {L : List (Int × Int)} (h : t ∈ rays b s L)
    (hd : ∀ d ∈ L, d.1 ≠ 0 ∨ d.2 ≠ 0) : t ≠ s := by
  unfold rays at h
  rw [List.mem_flatMap] at h
  obtain ⟨⟨df, dr⟩, hdm, hr⟩ := h
  obtain ⟨g1, g2, _, _, g5, _⟩ := ray_slant hr
  rcases hd (df, dr) hdm with h1 | h2
  · by_cases hlt : df < 0
    · exact fun he => by subst he; have := g2 hlt; omega
    · have hgt : 0 < df := by omega
      exact fun he => by subst he; have := g1 hgt; omega
  · by_cases hlt : dr < 0
    · exact fun he => by subst he; have := g5 hlt; omega
    · have hgt : 0 < dr := by omega
      obtain ⟨_, _, _, g4, _, _⟩ := ray_slant hr
      exact fun he => by subst he; have := g4 hgt; omega

theorem pawnAttD_ne (c : Color) : ∀ d ∈ [(1, c.fwd), (-1, c.fwd)], d.1 ≠ 0 ∨ d.2 ≠ 0 := by
  rintro ⟨df, dr⟩ hd
  simp at hd
  rcases hd with ⟨h1, _⟩ | ⟨h1, _⟩
  · subst h1
    exact .inl (show (1 : Int) ≠ 0 by decide)
  · subst h1
    exact .inl (show (-1 : Int) ≠ 0 by decide)

theorem attacks_irrefl {b : Board} {s t : Sq} {q : Piece} (h : t ∈ attacks b s q) : t ≠ s := by
  unfold attacks at h
  split at h
  · exact steps_ne h (pawnAttD_ne q.color)
  · exact steps_ne h (fun d hd => dir_ne_of_mem (.inl hd))
  · exact steps_ne h (fun d hd => dir_ne_of_mem (.inr (.inr (.inr hd))))
  · exact rays_ne h (fun d hd => dir_ne_of_mem (.inr (.inl hd)))
  · exact rays_ne h (fun d hd => dir_ne_of_mem (.inr (.inr (.inl hd))))
  · exact rays_ne h (fun d hd => dir_ne_of_mem (.inr (.inr (.inr hd))))

theorem pawnMoves_src_ne_dst {p : Pos} {s : Sq} {c : Color} {m : Move}
    (h : m ∈ pawnMoves p s c) : m.src ≠ m.dst := by
  have hfw : c.fwd = 1 ∨ c.fwd = -1 := by cases c <;> decide
  rcases pawnMoves_cases h with ⟨t, hof, _, hmk⟩ | ⟨t, hst, _, hmk⟩ | ⟨t, _, _, hof2, _, hm⟩
  · have hsd : m.src = s ∧ m.dst = t := by
      split at hmk
      · obtain ⟨k, _, hm⟩ := hmk
        rw [hm]
        exact ⟨rfl, rfl⟩
      · rw [hmk]
        exact ⟨rfl, rfl⟩
    intro he
    rw [hsd.1, hsd.2] at he
    have cr := (off_coords hof).2
    rw [← he] at cr
    rcases hfw with hfw | hfw <;> rw [hfw] at cr <;> omega
  · have hsd : m.src = s ∧ m.dst = t := by
      split at hmk
      · obtain ⟨k, _, hm⟩ := hmk
        rw [hm]
        exact ⟨rfl, rfl⟩
      · rw [hmk]
        exact ⟨rfl, rfl⟩
    intro he
    rw [hsd.1, hsd.2] at he
    exact steps_ne hst (pawnAttD_ne c) he.symm
  · obtain ⟨hms, hmd, _⟩ := move_eq hm
    intro he
    rw [hms, hmd] at he
    have cr := (off_coords hof2).2
    rw [← he] at cr
    rcases hfw with hfw | hfw <;> rw [hfw] at cr <;> omega

theorem pseudo_src_ne_dst {p : Pos} {m : Move} (h : m ∈ pseudo p) : m.src ≠ m.dst := by
  rcases pseudo_cases h with ⟨s, q, hbs, hcol, hpm⟩ | hc
  · rcases pieceMoves_cases hpm with ⟨hk, hpw⟩ | ⟨_, hsrc, _, hdfl⟩
    · exact pawnMoves_src_ne_dst hpw
    · rw [List.mem_filter] at hdfl
      have hne := attacks_irrefl hdfl.1
      rw [← hsrc] at hne
      exact fun he => hne he.symm
  · obtain ⟨hsrc, _, _, _, hside⟩ := castleMoves_cases hc
    rcases hside with ⟨hdst, _, _, _, _⟩ | ⟨hdst, _, _, _, _, _⟩
    · rw [hsrc, hdst]
      exact sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide)
    · rw [hsrc, hdst]
      exact sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide)

theorem dist_self (a b : Sq) : dist a b = dist b a := by
  unfold dist
  congr 1 <;> omega

theorem mem_steps_queenD_of_dist {a t : Sq} (hd : dist a t ≤ 1) (hne : a ≠ t) :
    t ∈ steps a queenD := by
  have hb : (-1 : Int) ≤ (t.file : Int) - a.file ∧ (t.file : Int) - a.file ≤ 1 ∧
      (-1 : Int) ≤ (t.rank : Int) - a.rank ∧ (t.rank : Int) - a.rank ≤ 1 := by
    simp only [dist] at hd
    omega
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hf1 : (t.file : Int) - a.file = -1 ∨ (t.file : Int) - a.file = 0 ∨
      (t.file : Int) - a.file = 1 := by omega
  have hr1 : (t.rank : Int) - a.rank = -1 ∨ (t.rank : Int) - a.rank = 0 ∨
      (t.rank : Int) - a.rank = 1 := by omega
  have hne00 : ¬((t.file : Int) - a.file = 0 ∧ (t.rank : Int) - a.rank = 0) := by
    rintro ⟨h1, h2⟩
    apply hne
    apply sq_ext <;> omega
  have mk (df dr : Int) (hdm : (df, dr) ∈ queenD)
      (hf : (t.file : Int) - a.file = df) (hr : (t.rank : Int) - a.rank = dr) :
      t ∈ steps a queenD :=
    List.mem_filterMap.mpr ⟨(df, dr), hdm, off_int (by omega) (by omega)⟩
  rcases hf1 with f | f | f <;> rcases hr1 with r | r | r
  · exact mk (-1) (-1) (by decide) f r
  · exact mk (-1) 0 (by decide) f r
  · exact mk (-1) 1 (by decide) f r
  · exact mk 0 (-1) (by decide) f r
  · exact absurd ⟨f, r⟩ hne00
  · exact mk 0 1 (by decide) f r
  · exact mk 1 (-1) (by decide) f r
  · exact mk 1 0 (by decide) f r
  · exact mk 1 1 (by decide) f r

theorem king_attacked_of_dist {b : Board} {a t : Sq} {c d : Color} (hcd : c ≠ d)
    (ha : b a = some ⟨c, .king⟩) (ht : b t = some ⟨d, .king⟩) (hd : dist a t ≤ 1) :
    attacked b t c = true := by
  have hne : a ≠ t := by
    intro he
    rw [← he, ha] at ht
    simp at ht
    exact hcd ht
  exact attacked_of_mem ha rfl (mem_steps_queenD_of_dist hd hne)

theorem apart_of_safe (q : Pos) (hk : ∀ c, cnt q.board c .king = 1) (hs : inCheck q q.turn.opp = false) :
    1 < dist (kingSq q .white) (kingSq q .black) := by
  rcases (by omega : dist (kingSq q .white) (kingSq q .black) ≤ 1 ∨
      1 < dist (kingSq q .white) (kingSq q .black)) with h | h
  · obtain ⟨hbw, _⟩ := kingSq_spec q .white (hk .white)
    obtain ⟨hbb, _⟩ := kingSq_spec q .black (hk .black)
    have hd : dist (kingSq q .black) (kingSq q .white) ≤ 1 := by rw [dist_self]; exact h
    have hwhite : attacked q.board (kingSq q .white) .black = true :=
      king_attacked_of_dist (by decide) hbb hbw hd
    have hblack : attacked q.board (kingSq q .black) .white = true :=
      king_attacked_of_dist (by decide) hbw hbb h
    cases ht : q.turn with
    | white =>
      have hic : inCheck q .black = true := by
        rw [inCheck_iff_attacked q .black (hk .black)]
        exact hblack
      rw [ht] at hs
      simp only [Color.opp] at hs
      exact absurd hic (by rw [hs]; decide)
    | black =>
      have hic : inCheck q .white = true := by
        rw [inCheck_iff_attacked q .white (hk .white)]
        exact hwhite
      rw [ht] at hs
      simp only [Color.opp] at hs
      exact absurd hic (by rw [hs]; decide)
  · exact h

theorem admissible_initial : Admissible initial :=
  (admB_iff initial).mp (by decide +kernel)

theorem filter_ext {l : List Sq} {P Q : Sq → Bool} (h : ∀ s ∈ l, P s = Q s) :
    l.filter P = l.filter Q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.filter_cons, List.filter_cons, ih (fun s hs => h s (List.mem_cons_of_mem a hs)),
      h a (List.mem_cons.mpr (.inl rfl))]

theorem sq_ne_file {a b : Sq} (h : a.file ≠ b.file) : a ≠ b := fun he => h (congrArg Sq.file he)

theorem sq_ne_rank {a b : Sq} (h : a.rank ≠ b.rank) : a ≠ b := fun he => h (congrArg Sq.rank he)

theorem bt_true : (true : Bool).toNat = 1 := rfl

theorem bt_false : (false : Bool).toNat = 0 := rfl

theorem filter_length_update {l : List Sq} (hnd : l.Nodup) {x : Sq} (hx : x ∈ l)
    (Q : Sq → Option Piece → Bool) (b : Board) (v : Option Piece) :
    (l.filter fun s => Q s (bupd b x v s)).length + (Q x (b x)).toNat =
      (l.filter fun s => Q s (b s)).length + (Q x v).toNat := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨ha, hl⟩ := hnd
    rcases List.mem_cons.mp hx with hax | hx
    · subst hax
      rw [List.filter_cons, List.filter_cons]
      have htl : l.filter (fun s => Q s (bupd b x v s)) = l.filter (fun s => Q s (b s)) := by
        apply filter_ext
        intro s hs
        rw [bupd_ne _ (fun he => by subst he; exact ha hs) v]
      rw [bupd_self, htl]
      cases h1 : Q x v <;> cases h2 : Q x (b x) <;>
        simp [h1, h2, bt_true, bt_false, List.length_cons]
    · rw [List.filter_cons, List.filter_cons]
      have hax : a ≠ x := fun he => by subst he; exact ha hx
      have hc' : Q a (bupd b x v a) = Q a (b a) := congrArg (Q a) (bupd_ne _ hax v)
      rw [hc']
      have ihh := ih hl hx
      cases hC : Q a (b a) <;> simp [hC, List.length_cons] <;> omega

theorem flen_update (Q : Sq → Option Piece → Bool) (b : Board) (x : Sq) (v : Option Piece) :
    (allSq.filter fun s => Q s (bupd b x v s)).length + (Q x (b x)).toNat =
      (allSq.filter fun s => Q s (b s)).length + (Q x v).toNat :=
  filter_length_update (List.nodup_finRange 64) (List.mem_finRange x) Q b v

theorem play_board_simple_eq (p : Pos) (m : Move) (hc : isCastle p m = false)
    (he : isEp p m = false) :
    (play p m).board = bupd (bupd p.board m.src none) m.dst (moved p m) := by
  funext s
  rw [play_board_simple p m hc he]
  by_cases h1 : s = m.dst
  · subst h1
    rw [if_pos rfl]
    simp [bupd]
  · rw [if_neg h1]
    by_cases h2 : s = m.src
    · subst h2
      rw [if_pos rfl]
      simp [bupd, h1]
    · rw [if_neg h2]
      simp [bupd, h1, h2]

theorem play_board_ep_eq (p : Pos) (m : Move) (he : isEp p m = true)
    (hds : m.dst ≠ m.src) (hdv : m.dst ≠ epVictim m) (hsv : m.src ≠ epVictim m) :
    (play p m).board = bupd (bupd (bupd p.board (epVictim m) none) m.src none) m.dst (moved p m) := by
  funext s
  rw [play_board_ep p m he]
  by_cases h1 : s = m.dst
  · subst h1
    rw [if_pos rfl]
    simp [bupd]
  · rw [if_neg h1]
    by_cases h2 : s = m.src
    · subst h2
      rw [if_pos (.inl rfl)]
      simp [bupd, hds.symm]
    · by_cases h3 : s = epVictim m
      · subst h3
        rw [if_pos (.inr rfl)]
        simp [bupd, hsv.symm, hdv.symm]
      · rw [if_neg (fun h => h.elim h2 h3)]
        simp [bupd, h1, h2, h3]

theorem play_board_castle_eq (p : Pos) (m : Move) (hc : isCastle p m = true)
    (hds : m.dst ≠ m.src) (hdt : m.dst ≠ rookTo m) (hdf : m.dst ≠ rookFrom m)
    (hst : m.src ≠ rookTo m) (hsf : m.src ≠ rookFrom m) (htf : rookTo m ≠ rookFrom m) :
    (play p m).board =
      bupd (bupd (bupd (bupd p.board (rookFrom m) none) (rookTo m) (p.board (rookFrom m)))
        m.src none) m.dst (moved p m) := by
  funext s
  rw [play_board_castle p m hc]
  by_cases h1 : s = m.dst
  · subst h1
    rw [if_pos rfl]
    simp [bupd]
  · rw [if_neg h1]
    by_cases h2 : s = m.src
    · subst h2
      rw [if_pos rfl]
      simp [bupd, hds.symm]
    · rw [if_neg h2]
      by_cases h3 : s = rookTo m
      · subst h3
        rw [if_pos rfl]
        simp [bupd, hdt.symm, hst.symm]
      · rw [if_neg h3]
        by_cases h4 : s = rookFrom m
        · subst h4
          rw [if_pos rfl]
          simp [bupd, hdf.symm, hsf.symm, htf.symm]
        · rw [if_neg h4]
          simp [bupd, h1, h2, h3, h4]

theorem flen_play_simple (p : Pos) (m : Move) (hc : isCastle p m = false) (he : isEp p m = false)
    (hsd : m.src ≠ m.dst) (Q : Sq → Option Piece → Bool) (hQ : ∀ x, Q x none = false) :
    (allSq.filter fun s => Q s ((play p m).board s)).length
        + (Q m.src (p.board m.src)).toNat + (Q m.dst (p.board m.dst)).toNat =
      (allSq.filter fun s => Q s (p.board s)).length + (Q m.dst (moved p m)).toNat := by
  rw [play_board_simple_eq p m hc he]
  have e1 := flen_update Q (bupd p.board m.src none) m.dst (moved p m)
  have e2 := flen_update Q p.board m.src none
  rw [bupd_ne _ (Ne.symm hsd)] at e1
  rw [hQ m.src, bt_false] at e2
  omega

theorem flen_play_ep (p : Pos) (m : Move) (he : isEp p m = true)
    (hds : m.dst ≠ m.src) (hdv : m.dst ≠ epVictim m) (hsv : m.src ≠ epVictim m)
    (Q : Sq → Option Piece → Bool) (hQ : ∀ x, Q x none = false) :
    (allSq.filter fun s => Q s ((play p m).board s)).length
        + (Q m.src (p.board m.src)).toNat + (Q m.dst (p.board m.dst)).toNat
        + (Q (epVictim m) (p.board (epVictim m))).toNat =
      (allSq.filter fun s => Q s (p.board s)).length + (Q m.dst (moved p m)).toNat := by
  rw [play_board_ep_eq p m he hds hdv hsv]
  have e1 := flen_update Q (bupd (bupd p.board (epVictim m) none) m.src none) m.dst (moved p m)
  have e2 := flen_update Q (bupd p.board (epVictim m) none) m.src none
  have e3 := flen_update Q p.board (epVictim m) none
  rw [bupd_ne _ hds, bupd_ne _ hdv] at e1
  rw [bupd_ne _ hsv] at e2
  rw [hQ m.src, bt_false] at e2
  rw [hQ (epVictim m), bt_false] at e3
  omega

theorem flen_play_castle (p : Pos) (m : Move) (hc : isCastle p m = true)
    (hds : m.dst ≠ m.src) (hdt : m.dst ≠ rookTo m) (hdf : m.dst ≠ rookFrom m)
    (hst : m.src ≠ rookTo m) (hsf : m.src ≠ rookFrom m) (htf : rookTo m ≠ rookFrom m)
    (Q : Sq → Option Piece → Bool) (hQ : ∀ x, Q x none = false) :
    (allSq.filter fun s => Q s ((play p m).board s)).length
        + (Q m.src (p.board m.src)).toNat + (Q m.dst (p.board m.dst)).toNat
        + (Q (rookTo m) (p.board (rookTo m))).toNat
        + (Q (rookFrom m) (p.board (rookFrom m))).toNat =
      (allSq.filter fun s => Q s (p.board s)).length + (Q m.dst (moved p m)).toNat
        + (Q (rookTo m) (p.board (rookFrom m))).toNat := by
  rw [play_board_castle_eq p m hc hds hdt hdf hst hsf htf]
  have e1 := flen_update Q
    (bupd (bupd (bupd p.board (rookFrom m) none) (rookTo m) (p.board (rookFrom m))) m.src none)
    m.dst (moved p m)
  have e2 := flen_update Q (bupd (bupd p.board (rookFrom m) none) (rookTo m) (p.board (rookFrom m)))
    m.src none
  have e3 := flen_update Q (bupd p.board (rookFrom m) none) (rookTo m) (p.board (rookFrom m))
  have e4 := flen_update Q p.board (rookFrom m) none
  rw [bupd_ne _ hds, bupd_ne _ hdt, bupd_ne _ hdf] at e1
  rw [bupd_ne _ hst, bupd_ne _ hsf] at e2
  rw [hQ m.src, bt_false] at e2
  rw [bupd_ne _ htf] at e3
  rw [hQ (rookFrom m), bt_false] at e4
  omega

theorem moved_of_no_promo {p : Pos} {m : Move} (hp : m.promo = none) : moved p m = p.board m.src := by
  simp [moved, hp]

theorem moved_of_promo {p : Pos} {m : Move} {k : Kind} (hp : m.promo = some k) :
    moved p m = (p.board m.src).map fun q => ⟨q.color, k⟩ := by
  simp [moved, hp]

theorem moved_color (p : Pos) (m : Move) (c : Color) :
    (moved p m).any (·.color == c) = (p.board m.src).any (·.color == c) := by
  unfold moved
  cases hpr : m.promo with
  | none => rfl
  | some k =>
    cases hb : p.board m.src with
    | none => rfl
    | some q => rfl

theorem moved_king_beq {p : Pos} {m : Move} (h : m ∈ pseudo p) (c : Color) :
    (moved p m == some ⟨c, .king⟩) = (p.board m.src == some ⟨c, .king⟩) := by
  cases hpr : m.promo with
  | none => rw [moved_of_no_promo hpr]
  | some k =>
    obtain ⟨hbs, _, hkp, hkk⟩ := pseudo_promo h k hpr
    rw [moved_of_promo hpr, hbs]
    change ((some ⟨p.turn, k⟩ : Option Piece) == some ⟨c, .king⟩) =
      ((some ⟨p.turn, .pawn⟩ : Option Piece) == some ⟨c, .king⟩)
    have e1 : ((some ⟨p.turn, k⟩ : Option Piece) == some ⟨c, .king⟩) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      simp only [Option.some.injEq, Piece.mk.injEq] at he
      exact hkk he.2
    have e2 : ((some ⟨p.turn, .pawn⟩ : Option Piece) == some ⟨c, .king⟩) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      simp only [Option.some.injEq, Piece.mk.injEq] at he
      exact absurd he.2 (by decide)
    rw [e1, e2]

theorem board_dst_ne {p : Pos} {m : Move} (h : m ∈ pseudo p) (k : Kind) :
    (p.board m.dst == some ⟨p.turn, k⟩) = false := by
  rw [beq_eq_false_iff_ne]
  intro hd
  have h1 := pseudo_dst h ⟨p.turn, k⟩ hd
  exact h1 rfl

theorem board_dst_ne_king {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ pseudo p) (c : Color) :
    (p.board m.dst == some ⟨c, .king⟩) = false := by
  rw [beq_eq_false_iff_ne]
  intro hdk
  by_cases hcc : c = p.turn
  · subst hcc
    exact absurd (beq_iff_eq.mpr hdk) (by rw [board_dst_ne h .king]; decide)
  · have hc2 : c = p.turn.opp := by
      cases c <;> cases ht : p.turn
      · rw [ht] at hcc
        exact absurd rfl hcc
      · rfl
      · rfl
      · rw [ht] at hcc
        exact absurd rfl hcc
    rw [hc2] at hdk
    exact pseudo_no_king_capture hA h hdk

theorem moved_turn {p : Pos} {m : Move} (h : m ∈ pseudo p) : ∃ k, moved p m = some ⟨p.turn, k⟩ := by
  obtain ⟨q, hsrc, hcol⟩ := pseudo_src h
  cases hpr : m.promo with
  | none =>
    rw [moved_of_no_promo hpr, hsrc, ← hcol]
    exact ⟨q.kind, rfl⟩
  | some k =>
    refine ⟨k, ?_⟩
    rw [moved_of_promo hpr, hsrc]
    show (some (Piece.mk q.color k) : Option Piece) = some (Piece.mk p.turn k)
    rw [hcol]

theorem moved_ne_opp {p : Pos} {m : Move} (h : m ∈ pseudo p) (k : Kind) :
    (moved p m == some ⟨p.turn.opp, k⟩) = false := by
  obtain ⟨k', hk'⟩ := moved_turn h
  rw [hk', beq_eq_false_iff_ne]
  intro he
  simp only [Option.some.injEq, Piece.mk.injEq] at he
  cases ht : p.turn <;> rw [ht] at he <;> simp [Color.opp] at he

def cntP (c : Color) (k : Kind) (s : Sq) (o : Option Piece) : Bool := o == some ⟨c, k⟩

def menP (c : Color) (s : Sq) (o : Option Piece) : Bool := o.any (fun x => x.color == c)

def cntBP (c : Color) (par : Nat) (s : Sq) (o : Option Piece) : Bool :=
  (o == some ⟨c, .bishop⟩) && parity s == par

theorem cnt_play_simple (p : Pos) (m : Move) (hc : isCastle p m = false) (he : isEp p m = false)
    (hsd : m.src ≠ m.dst) (c : Color) (k : Kind) :
    cnt (play p m).board c k + (p.board m.src == some ⟨c, k⟩).toNat +
        (p.board m.dst == some ⟨c, k⟩).toNat =
      cnt p.board c k + (moved p m == some ⟨c, k⟩).toNat := by
  unfold cnt countSq
  exact flen_play_simple p m hc he hsd (cntP c k) (fun x => rfl)

theorem men_play_simple (p : Pos) (m : Move) (hc : isCastle p m = false) (he : isEp p m = false)
    (hsd : m.src ≠ m.dst) (c : Color) :
    men (play p m).board c + ((p.board m.src).any (·.color == c)).toNat +
        ((p.board m.dst).any (·.color == c)).toNat =
      men p.board c + ((moved p m).any (·.color == c)).toNat := by
  unfold men countSq
  exact flen_play_simple p m hc he hsd (menP c) (fun x => rfl)

theorem cntB_play_simple (p : Pos) (m : Move) (hc : isCastle p m = false) (he : isEp p m = false)
    (hsd : m.src ≠ m.dst) (c : Color) (par : Nat) :
    cntB (play p m).board c par +
        ((p.board m.src == some ⟨c, .bishop⟩) && parity m.src == par).toNat +
        ((p.board m.dst == some ⟨c, .bishop⟩) && parity m.dst == par).toNat =
      cntB p.board c par + ((moved p m == some ⟨c, .bishop⟩) && parity m.dst == par).toNat := by
  unfold cntB
  exact flen_play_simple p m hc he hsd (cntBP c par) (fun x => rfl)

theorem castle_geom {p : Pos} {m : Move} (h : m ∈ pseudo p) (hc : isCastle p m = true) :
    m.src = sq 4 p.turn.home ∧ m.promo = none ∧
    p.board m.src = some ⟨p.turn, .king⟩ ∧ p.board m.dst = none ∧
    p.board (rookTo m) = none ∧ p.board (rookFrom m) = some ⟨p.turn, .rook⟩ ∧
    ((m.dst = sq 6 p.turn.home ∧ rookFrom m = sq 7 p.turn.home ∧ rookTo m = sq 5 p.turn.home) ∨
     (m.dst = sq 2 p.turn.home ∧ rookFrom m = sq 0 p.turn.home ∧ rookTo m = sq 3 p.turn.home)) := by
  obtain ⟨hpn, hsrc, hbK, hbd, hrtnone, hrfr, hside⟩ := pseudo_castle h hc
  refine ⟨hsrc, hpn, hbK, hbd, hrtnone, hrfr, ?_⟩
  rcases hside with ⟨hdst, hck⟩ | ⟨hdst, hcq⟩
  · have hcond : (m.src.file + 2 == m.dst.file) = true := by
      rw [hsrc, hdst, sq_file 4 _ (by decide) (home_lt _), sq_file 6 _ (by decide) (home_lt _)]
      decide
    refine .inl ⟨hdst, ?_, ?_⟩
    · unfold rookFrom
      rw [if_pos hcond, hsrc, sq_rank 4 _ (by decide) (home_lt _)]
    · unfold rookTo
      rw [if_pos hcond, hsrc, sq_rank 4 _ (by decide) (home_lt _)]
  · have hcond : (m.src.file + 2 == m.dst.file) = false := by
      rw [hsrc, hdst, sq_file 4 _ (by decide) (home_lt _), sq_file 2 _ (by decide) (home_lt _)]
      decide
    refine .inr ⟨hdst, ?_, ?_⟩
    · unfold rookFrom
      rw [if_neg (by simp [hcond]), hsrc, sq_rank 4 _ (by decide) (home_lt _)]
    · unfold rookTo
      rw [if_neg (by simp [hcond]), hsrc, sq_rank 4 _ (by decide) (home_lt _)]

theorem castle_ne {p : Pos} {m : Move} (h : m ∈ pseudo p) (hc : isCastle p m = true) :
    m.dst ≠ m.src ∧ m.dst ≠ rookTo m ∧ m.dst ≠ rookFrom m ∧
    m.src ≠ rookTo m ∧ m.src ≠ rookFrom m ∧ rookTo m ≠ rookFrom m := by
  obtain ⟨hsrc, _, _, _, _, _, hside⟩ := castle_geom h hc
  rcases hside with ⟨hdst, hrf, hrt⟩ | ⟨hdst, hrf, hrt⟩
  · rw [hdst, hrf, hrt, hsrc]
    exact ⟨sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide),
      sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide),
      sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide),
      sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide),
      sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide),
      sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide)⟩
  · rw [hdst, hrf, hrt, hsrc]
    exact ⟨sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide),
      sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide),
      sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide),
      sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide),
      sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide),
      sq_ne_of_file_ne (by decide) (home_lt _) (by decide) (home_lt _) (by decide)⟩

theorem cnt_play_ep (p : Pos) (m : Move) (he : isEp p m = true)
    (hds : m.dst ≠ m.src) (hdv : m.dst ≠ epVictim m) (hsv : m.src ≠ epVictim m)
    (c : Color) (k : Kind) :
    cnt (play p m).board c k + (p.board m.src == some ⟨c, k⟩).toNat +
        (p.board m.dst == some ⟨c, k⟩).toNat +
        (p.board (epVictim m) == some ⟨c, k⟩).toNat =
      cnt p.board c k + (moved p m == some ⟨c, k⟩).toNat := by
  unfold cnt countSq
  exact flen_play_ep p m he hds hdv hsv (cntP c k) (fun x => rfl)

theorem cnt_play_castle (p : Pos) (m : Move) (hc : isCastle p m = true)
    (hds : m.dst ≠ m.src) (hdt : m.dst ≠ rookTo m) (hdf : m.dst ≠ rookFrom m)
    (hst : m.src ≠ rookTo m) (hsf : m.src ≠ rookFrom m) (htf : rookTo m ≠ rookFrom m)
    (c : Color) (k : Kind) :
    cnt (play p m).board c k + (p.board m.src == some ⟨c, k⟩).toNat +
        (p.board m.dst == some ⟨c, k⟩).toNat +
        (p.board (rookTo m) == some ⟨c, k⟩).toNat +
        (p.board (rookFrom m) == some ⟨c, k⟩).toNat =
      cnt p.board c k + (moved p m == some ⟨c, k⟩).toNat +
        (p.board (rookFrom m) == some ⟨c, k⟩).toNat := by
  unfold cnt countSq
  exact flen_play_castle p m hc hds hdt hdf hst hsf htf (cntP c k) (fun x => rfl)

theorem men_play_ep (p : Pos) (m : Move) (he : isEp p m = true)
    (hds : m.dst ≠ m.src) (hdv : m.dst ≠ epVictim m) (hsv : m.src ≠ epVictim m)
    (c : Color) :
    men (play p m).board c + ((p.board m.src).any (·.color == c)).toNat +
        ((p.board m.dst).any (·.color == c)).toNat +
        ((p.board (epVictim m)).any (·.color == c)).toNat =
      men p.board c + ((moved p m).any (·.color == c)).toNat := by
  unfold men countSq
  exact flen_play_ep p m he hds hdv hsv (menP c) (fun x => rfl)

theorem men_play_castle (p : Pos) (m : Move) (hc : isCastle p m = true)
    (hds : m.dst ≠ m.src) (hdt : m.dst ≠ rookTo m) (hdf : m.dst ≠ rookFrom m)
    (hst : m.src ≠ rookTo m) (hsf : m.src ≠ rookFrom m) (htf : rookTo m ≠ rookFrom m)
    (c : Color) :
    men (play p m).board c + ((p.board m.src).any (·.color == c)).toNat +
        ((p.board m.dst).any (·.color == c)).toNat +
        ((p.board (rookTo m)).any (·.color == c)).toNat +
        ((p.board (rookFrom m)).any (·.color == c)).toNat =
      men p.board c + ((moved p m).any (·.color == c)).toNat +
        ((p.board (rookFrom m)).any (·.color == c)).toNat := by
  unfold men countSq
  exact flen_play_castle p m hc hds hdt hdf hst hsf htf (menP c) (fun x => rfl)

theorem cntB_play_ep (p : Pos) (m : Move) (he : isEp p m = true)
    (hds : m.dst ≠ m.src) (hdv : m.dst ≠ epVictim m) (hsv : m.src ≠ epVictim m)
    (c : Color) (par : Nat) :
    cntB (play p m).board c par +
        ((p.board m.src == some ⟨c, .bishop⟩) && parity m.src == par).toNat +
        ((p.board m.dst == some ⟨c, .bishop⟩) && parity m.dst == par).toNat +
        ((p.board (epVictim m) == some ⟨c, .bishop⟩) && parity (epVictim m) == par).toNat =
      cntB p.board c par + ((moved p m == some ⟨c, .bishop⟩) && parity m.dst == par).toNat := by
  unfold cntB
  exact flen_play_ep p m he hds hdv hsv (cntBP c par) (fun x => rfl)

theorem cntB_play_castle (p : Pos) (m : Move) (hc : isCastle p m = true)
    (hds : m.dst ≠ m.src) (hdt : m.dst ≠ rookTo m) (hdf : m.dst ≠ rookFrom m)
    (hst : m.src ≠ rookTo m) (hsf : m.src ≠ rookFrom m) (htf : rookTo m ≠ rookFrom m)
    (c : Color) (par : Nat) :
    cntB (play p m).board c par +
        ((p.board m.src == some ⟨c, .bishop⟩) && parity m.src == par).toNat +
        ((p.board m.dst == some ⟨c, .bishop⟩) && parity m.dst == par).toNat +
        ((p.board (rookTo m) == some ⟨c, .bishop⟩) && parity (rookTo m) == par).toNat +
        ((p.board (rookFrom m) == some ⟨c, .bishop⟩) && parity (rookFrom m) == par).toNat =
      cntB p.board c par + ((moved p m == some ⟨c, .bishop⟩) && parity m.dst == par).toNat +
        ((p.board (rookFrom m) == some ⟨c, .bishop⟩) && parity (rookTo m) == par).toNat := by
  unfold cntB
  exact flen_play_castle p m hc hds hdt hdf hst hsf htf (cntBP c par) (fun x => rfl)

theorem play_kings {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ legalMoves p) (c : Color) :
    cnt (play p m).board c .king = 1 := by
  obtain ⟨hmem, hic⟩ := mem_legalMoves h
  have hsd := pseudo_src_ne_dst hmem
  have mkv := moved_king_beq hmem c
  have hdk := board_dst_ne_king hA hmem c
  have hk1 := hA.kings c
  by_cases hcas : isCastle p m = true
  · obtain ⟨hsrc, hpn, hbK, hbd, hrto, hrfr, hside⟩ := castle_geom hmem hcas
    obtain ⟨hds', hdt, hdf, hst, hsf, htf⟩ := castle_ne hmem hcas
    have e1 := cnt_play_castle p m hcas hds' hdt hdf hst hsf htf c .king
    have hrto0 : (p.board (rookTo m) == some ⟨c, .king⟩) = false := by
      rw [hrto]
      rfl
    have hrf0 : (p.board (rookFrom m) == some ⟨c, .king⟩) = false := by
      rw [hrfr, beq_eq_false_iff_ne]
      intro he
      simp only [Option.some.injEq, Piece.mk.injEq] at he
      exact absurd he.2 (by decide)
    rw [mkv, hdk, hrto0, hrf0] at e1
    simp only [bt_false] at e1
    omega
  · have hcf : isCastle p m = false := by
      cases h2 : isCastle p m with
      | false => rfl
      | true => exact absurd h2 hcas
    by_cases hep : isEp p m = true
    · obtain ⟨hepq, hvic, hpn, hrank⟩ := pseudo_ep hA hmem hep
      have hvr : (epVictim m).rank = m.src.rank := by
        unfold epVictim
        rw [sq_rank _ _ (file_lt m.dst) (rank_lt m.src)]
      have hdv : m.dst ≠ epVictim m := by
        apply sq_ne_rank
        rw [hvr]
        intro heq
        rcases color_cases p.turn with ⟨_, hfw, _, _, _, _⟩ | ⟨_, hfw, _, _, _, _⟩ <;>
          rw [hfw] at hrank <;> omega
      have hsv : m.src ≠ epVictim m := by
        apply sq_ne_file
        have hvf : (epVictim m).file = m.dst.file := by
          unfold epVictim
          rw [sq_file _ _ (file_lt m.dst) (rank_lt m.src)]
        rw [hvf]
        unfold isEp at hep
        rw [Bool.and_eq_true, Bool.and_eq_true] at hep
        exact bne_iff_ne.mp hep.1.2
      have e1 := cnt_play_ep p m hep (Ne.symm hsd) hdv hsv c .king
      have hsrc0 : (p.board m.src == some ⟨c, .king⟩) = false := by
        unfold isEp at hep
        rw [Bool.and_eq_true, Bool.and_eq_true] at hep
        have hpa := hep.1.1
        cases hb : p.board m.src with
        | none => rfl
        | some q =>
          have hqk : (q.kind == Kind.pawn) = true := by rw [hb] at hpa; exact hpa
          rw [beq_eq_false_iff_ne]
          intro he
          simp only [Option.some.injEq] at he
          have h2 : q.kind = Kind.king := congrArg Piece.kind he
          rw [h2] at hqk
          simp at hqk
      have hvic0 : (p.board (epVictim m) == some ⟨c, .king⟩) = false := by
        rw [hvic, beq_eq_false_iff_ne]
        intro he
        simp only [Option.some.injEq, Piece.mk.injEq] at he
        exact absurd he.2 (by decide)
      rw [mkv, hsrc0, hdk, hvic0] at e1
      simp only [bt_false] at e1
      omega
    · have hef : isEp p m = false := by
        cases h2 : isEp p m with
        | false => rfl
        | true => exact absurd h2 hep
      have e1 := cnt_play_simple p m hcf hef hsd c .king
      rw [mkv, hdk] at e1
      simp only [bt_false] at e1
      omega

theorem play_safe {p : Pos} {m : Move} (h : m ∈ legalMoves p) :
    inCheck (play p m) (play p m).turn.opp = false := by
  obtain ⟨_, hic⟩ := mem_legalMoves h
  rw [play_turn, opp_opp]
  exact hic

theorem ep_pawn_src {p : Pos} {m : Move} (h : m ∈ pseudo p) (he : isEp p m = true) :
    p.board m.src = some ⟨p.turn, .pawn⟩ := by
  obtain ⟨q, hsrc, hcol⟩ := pseudo_src h
  unfold isEp at he
  obtain ⟨he1, _⟩ := (Bool.and_eq_true _ _).mp he
  obtain ⟨hpa, _⟩ := (Bool.and_eq_true _ _).mp he1
  rw [hsrc, Option.any_some] at hpa
  have hqk : q.kind = Kind.pawn := beq_iff_eq.mp hpa
  have h2 : q = ⟨p.turn, .pawn⟩ := by
    have h3 : q = ⟨q.color, q.kind⟩ := rfl
    rw [h3, hcol, hqk]
  rw [hsrc, h2]

theorem ep_ne {p : Pos} {m : Move} (h : m ∈ pseudo p) (he : isEp p m = true) :
    m.dst ≠ m.src ∧ m.dst ≠ epVictim m ∧ m.src ≠ epVictim m := by
  have hsd := pseudo_src_ne_dst h
  have hsrc := ep_pawn_src h he
  unfold isEp at he
  rw [Bool.and_eq_true, Bool.and_eq_true] at he
  have hsf' : m.src.file ≠ m.dst.file := bne_iff_ne.mp he.1.2
  have hvr : (epVictim m).rank = m.src.rank := by
    unfold epVictim
    rw [sq_rank _ _ (file_lt m.dst) (rank_lt m.src)]
  have hvf : (epVictim m).file = m.dst.file := by
    unfold epVictim
    rw [sq_file _ _ (file_lt m.dst) (rank_lt m.src)]
  have hrank := pseudo_pawn_rank h hsrc
  refine ⟨Ne.symm hsd, ?_, ?_⟩
  · apply sq_ne_rank
    rw [hvr]
    intro heq
    rcases hrank with hr | ⟨hph, hr, hfe⟩
    · rcases color_cases p.turn with ⟨_, hfw, _, _, _, _⟩ | ⟨_, hfw, _, _, _, _⟩ <;>
        rw [hfw] at hr <;> omega
    · exact hsf' hfe.symm
  · apply sq_ne_file
    rw [hvf]
    exact hsf'

theorem sq_ne_of_board_ne {b : Board} {s u : Sq} {p₁ p₂ : Piece} (hs : b s = some p₁)
    (hu : b u = some p₂) (h : p₁ ≠ p₂) : s ≠ u := fun he => by
  rw [he] at hs
  rw [hu] at hs
  injection hs with hs'
  exact h hs'.symm

theorem play_men {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ legalMoves p) (c : Color) :
    men (play p m).board c ≤ men p.board c := by
  obtain ⟨hmem, _⟩ := mem_legalMoves h
  have hsd := pseudo_src_ne_dst hmem
  by_cases hcas : isCastle p m = true
  · obtain ⟨hds', hdt, hdf, hst, hsf, htf⟩ := castle_ne hmem hcas
    have e := men_play_castle p m hcas hds' hdt hdf hst hsf htf c
    rw [moved_color p m c] at e
    omega
  · have hcf : isCastle p m = false := by
      cases h2 : isCastle p m with
      | false => rfl
      | true => exact absurd h2 hcas
    by_cases hep : isEp p m = true
    · obtain ⟨h1, h2, h3⟩ := ep_ne hmem hep
      have e := men_play_ep p m hep h1 h2 h3 c
      rw [moved_color p m c] at e
      omega
    · have hef : isEp p m = false := by
        cases h2 : isEp p m with
        | false => rfl
        | true => exact absurd h2 hep
      have e := men_play_simple p m hcf hef hsd c
      rw [moved_color p m c] at e
      omega

theorem dst_back_forces_promo {p : Pos} {m : Move} (h : m ∈ pseudo p)
    (hsrc : p.board m.src = some ⟨p.turn, .pawn⟩) (hr : m.dst.rank = 0 ∨ m.dst.rank = 7) :
    m.promo.isSome := by
  have hsl := rank_lt m.src
  rcases color_cases p.turn with ⟨hT, hfw, hph, hl, _, _⟩ | ⟨hT, hfw, hph, hl, _, _⟩
  · rcases hr with h0 | h7
    · exfalso
      rcases pseudo_pawn_rank h hsrc with hr1 | ⟨_, hr1, _⟩ <;> rw [hfw] at hr1 <;> omega
    · exact pseudo_pawn_last h hsrc (by rw [hl]; exact h7)
  · rcases hr with h0 | h7
    · exact pseudo_pawn_last h hsrc (by rw [hl]; exact h0)
    · exfalso
      rcases pseudo_pawn_rank h hsrc with hr1 | ⟨_, hr1, _⟩ <;> rw [hfw] at hr1 <;> omega

theorem play_noBackPawn {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ legalMoves p) :
    ∀ s : Sq, ∀ c, (s.rank = 0 ∨ s.rank = 7) → (play p m).board s ≠ some ⟨c, .pawn⟩ := by
  obtain ⟨hmem, _⟩ := mem_legalMoves h
  intro s c hr hbs
  have hsd := pseudo_src_ne_dst hmem
  by_cases hcas : isCastle p m = true
  · obtain ⟨hsrc, hpn, hbK, hbd, hrto, hrfr, hside⟩ := castle_geom hmem hcas
    rw [play_board_castle p m hcas] at hbs
    by_cases h1 : s = m.dst
    · rw [if_pos h1, moved_of_no_promo hpn, hbK] at hbs
      simp at hbs
    · by_cases h2 : s = m.src
      · rw [if_neg h1, if_pos h2] at hbs
        simp at hbs
      · by_cases h3 : s = rookTo m
        · rw [if_neg h1, if_neg h2, if_pos h3, hrfr] at hbs
          simp at hbs
        · by_cases h4 : s = rookFrom m
          · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4] at hbs
            simp at hbs
          · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4] at hbs
            exact hA.noBackPawn s c hr hbs
  · have hcf : isCastle p m = false := by
      cases h2 : isCastle p m with
      | false => rfl
      | true => exact absurd h2 hcas
    by_cases hep : isEp p m = true
    · obtain ⟨hepq, hvic, hpn, hrank⟩ := pseudo_ep hA hmem hep
      rw [play_board_ep p m hep] at hbs
      by_cases h1 : s = m.dst
      · subst h1
        rw [if_pos rfl, moved_of_no_promo hpn, ep_pawn_src hmem hep] at hbs
        exact absurd (dst_back_forces_promo hmem (ep_pawn_src hmem hep) hr) (by rw [hpn]; decide)
      · by_cases h2 : s = m.src ∨ s = epVictim m
        · rw [if_neg h1, if_pos h2] at hbs
          simp at hbs
        · rw [if_neg h1, if_neg h2] at hbs
          exact hA.noBackPawn s c hr hbs
    · have hef : isEp p m = false := by
        cases h2 : isEp p m with
        | false => rfl
        | true => exact absurd h2 hep
      rw [play_board_simple p m hcf hef] at hbs
      by_cases h1 : s = m.dst
      · subst h1
        rw [if_pos rfl] at hbs
        cases hpr : m.promo with
        | none =>
          rw [moved_of_no_promo hpr] at hbs
          obtain ⟨q, hsrcq, hcol⟩ := pseudo_src hmem
          rw [hsrcq] at hbs
          simp only [Option.some.injEq] at hbs
          subst hbs
          have hcT : c = p.turn := hcol
          subst hcT
          exact absurd (dst_back_forces_promo hmem hsrcq hr) (by rw [hpr]; decide)
        | some k =>
          obtain ⟨_, _, hkp, _⟩ := pseudo_promo hmem k hpr
          obtain ⟨q, hsrcq, hcol⟩ := pseudo_src hmem
          rw [moved_of_promo hpr, hsrcq] at hbs
          have hbq : (some (Piece.mk q.color k)) = some ⟨c, .pawn⟩ := hbs
          simp only [Option.some.injEq, Piece.mk.injEq] at hbq
          exact hkp hbq.2
      · by_cases h2 : s = m.src
        · rw [if_neg h1, if_pos h2] at hbs
          simp at hbs
        · rw [if_neg h1, if_neg h2] at hbs
          exact hA.noBackPawn s c hr hbs

theorem nbeq (c : Color) (k : Kind) : ((none : Option Piece) == some ⟨c, k⟩) = false := by
  rw [beq_eq_false_iff_ne]
  simp

theorem beq_kind_ne (c : Color) (k₁ k₂ : Kind) (h : k₁ ≠ k₂) :
    ((some ⟨c, k₁⟩ : Option Piece) == some ⟨c, k₂⟩) = false := by
  rw [beq_eq_false_iff_ne]
  intro he
  simp only [Option.some.injEq, Piece.mk.injEq] at he
  exact h he.2

theorem beq_color_ne (c₁ c₂ : Color) (k₁ k₂ : Kind) (h : c₁ ≠ c₂) :
    ((some ⟨c₁, k₁⟩ : Option Piece) == some ⟨c₂, k₂⟩) = false := by
  rw [beq_eq_false_iff_ne]
  intro he
  simp only [Option.some.injEq, Piece.mk.injEq] at he
  exact h he.1

theorem opp_ne_self (c : Color) : c.opp ≠ c := by
  cases c <;> decide

theorem ne_opp (c : Color) : c ≠ c.opp := by
  cases c <;> decide

theorem bishop_indicator_no_promo {p : Pos} {m : Move} (hmem : m ∈ pseudo p) (hpn : m.promo = none)
    (par : Nat) :
    ((moved p m == some ⟨p.turn, .bishop⟩) && parity m.dst == par) =
      ((p.board m.src == some ⟨p.turn, .bishop⟩) && parity m.src == par) := by
  rw [moved_of_no_promo hpn]
  cases hx : (p.board m.src == some ⟨p.turn, .bishop⟩) with
  | false => rfl
  | true =>
    rw [beq_iff_eq] at hx
    rw [pseudo_bishop_parity hmem hx]

theorem play_material_other {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ legalMoves p) :
    excess (play p m).board p.turn.opp ≤ excess p.board p.turn.opp := by
  obtain ⟨hmem, _⟩ := mem_legalMoves h
  have hsd := pseudo_src_ne_dst hmem
  apply excess_mono _
  · intro k
    by_cases hcas : isCastle p m = true
    · obtain ⟨hds', hdt, hdf, hst, hsf, htf⟩ := castle_ne hmem hcas
      obtain ⟨_, _, _, _, _, hrfr, _⟩ := castle_geom hmem hcas
      have e := cnt_play_castle p m hcas hds' hdt hdf hst hsf htf p.turn.opp k
      rw [moved_ne_opp hmem k, hrfr, beq_color_ne _ _ _ _ (ne_opp _)] at e
      simp only [bt_false] at e
      omega
    · have hcf : isCastle p m = false := by
        cases h2 : isCastle p m with
        | false => rfl
        | true => exact absurd h2 hcas
      by_cases hep : isEp p m = true
      · obtain ⟨h1, h2, h3⟩ := ep_ne hmem hep
        have e := cnt_play_ep p m hep h1 h2 h3 p.turn.opp k
        rw [moved_ne_opp hmem k, bt_false] at e
        omega
      · have hef : isEp p m = false := by
          cases h2 : isEp p m with
          | false => rfl
          | true => exact absurd h2 hep
        have e := cnt_play_simple p m hcf hef hsd p.turn.opp k
        rw [moved_ne_opp hmem k, bt_false] at e
        omega
  · intro par
    by_cases hcas : isCastle p m = true
    · obtain ⟨hds', hdt, hdf, hst, hsf, htf⟩ := castle_ne hmem hcas
      obtain ⟨_, _, _, _, _, hrfr, _⟩ := castle_geom hmem hcas
      have e := cntB_play_castle p m hcas hds' hdt hdf hst hsf htf p.turn.opp par
      rw [moved_ne_opp hmem .bishop, hrfr, beq_color_ne _ _ _ _ (ne_opp _)] at e
      simp only [Bool.false_and, bt_false] at e
      omega
    · have hcf : isCastle p m = false := by
        cases h2 : isCastle p m with
        | false => rfl
        | true => exact absurd h2 hcas
      by_cases hep : isEp p m = true
      · obtain ⟨h1, h2, h3⟩ := ep_ne hmem hep
        have e := cntB_play_ep p m hep h1 h2 h3 p.turn.opp par
        rw [moved_ne_opp hmem .bishop] at e
        simp only [Bool.false_and, bt_false] at e
        omega
      · have hef : isEp p m = false := by
          cases h2 : isEp p m with
          | false => rfl
          | true => exact absurd h2 hep
        have e := cntB_play_simple p m hcf hef hsd p.turn.opp par
        rw [moved_ne_opp hmem .bishop] at e
        simp only [Bool.false_and, bt_false] at e
        omega

theorem play_castle_rights {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ legalMoves p) (c : Color) :
    ((play p m).castleK c = true →
      (play p m).board (sq 4 c.home) = some ⟨c, .king⟩ ∧ (play p m).board (sq 7 c.home) = some ⟨c, .rook⟩) ∧
    ((play p m).castleQ c = true →
      (play p m).board (sq 4 c.home) = some ⟨c, .king⟩ ∧ (play p m).board (sq 0 c.home) = some ⟨c, .rook⟩) := by
  obtain ⟨hmem, _⟩ := mem_legalMoves h
  have gpres (s : Sq) (k₀ : Kind) (hk0 : k₀ = .king ∨ k₀ = .rook)
      (hct : isCastle p m = true → c ≠ p.turn)
      (hsb : p.board s = some ⟨c, k₀⟩) (hsn : m.src ≠ s) (hdn : m.dst ≠ s) :
      (play p m).board s = some ⟨c, k₀⟩ := by
    by_cases hcas : isCastle p m = true
    · obtain ⟨hsrc, hpn, hbK, hbd, hrto, hrfr, hside⟩ := castle_geom hmem hcas
      have hct := hct hcas
      rw [play_board_castle p m hcas]
      by_cases h1 : s = m.dst
      · exact absurd h1.symm hdn
      · rw [if_neg h1]
        by_cases h2 : s = m.src
        · exact absurd h2.symm hsn
        · rw [if_neg h2]
          by_cases h3 : s = rookTo m
          · rw [if_pos h3]
            rw [h3] at hsb
            rw [hrto] at hsb
            simp at hsb
          · rw [if_neg h3]
            by_cases h4 : s = rookFrom m
            · rw [if_pos h4]
              rw [h4] at hsb
              rw [hrfr] at hsb
              simp only [Option.some.injEq, Piece.mk.injEq] at hsb
              exact absurd hsb.1.symm hct
            · rw [if_neg h4]
              exact hsb
    · have hcf : isCastle p m = false := by
        cases h2 : isCastle p m with
        | false => rfl
        | true => exact absurd h2 hcas
      by_cases hep : isEp p m = true
      · obtain ⟨_, hvic, _, _⟩ := pseudo_ep hA hmem hep
        rw [play_board_ep p m hep]
        by_cases h1 : s = m.dst
        · exact absurd h1.symm hdn
        · rw [if_neg h1]
          by_cases h2 : s = m.src ∨ s = epVictim m
          · rcases h2 with h2 | h2
            · exact absurd h2.symm hsn
            · rw [h2] at hsb
              rw [hvic] at hsb
              simp only [Option.some.injEq, Piece.mk.injEq] at hsb
              rcases hk0 with rfl | rfl <;> exact absurd hsb.2 (by decide)
          · rw [if_neg h2]
            exact hsb
      · have hef : isEp p m = false := by
          cases h2 : isEp p m with
          | false => rfl
          | true => exact absurd h2 hep
        rw [play_board_simple p m hcf hef]
        by_cases h1 : s = m.dst
        · exact absurd h1.symm hdn
        · rw [if_neg h1]
          by_cases h2 : s = m.src
          · exact absurd h2.symm hsn
          · rw [if_neg h2]
            exact hsb
  constructor
  · intro hK
    rw [play_castleK] at hK
    obtain ⟨hx1, n4⟩ := (Bool.and_eq_true _ _).mp hK
    obtain ⟨hx2, n3⟩ := (Bool.and_eq_true _ _).mp hx1
    obtain ⟨hx3, n2⟩ := (Bool.and_eq_true _ _).mp hx2
    obtain ⟨hck, n1⟩ := (Bool.and_eq_true _ _).mp hx3
    have hct : isCastle p m = true → c ≠ p.turn := by
      intro hcas he
      subst he
      obtain ⟨hsrc, hpn, hbK, hbd, hrto, hrfr, hside⟩ := castle_geom hmem hcas
      rw [hsrc] at n1
      simp at n1
    obtain ⟨b4, b7⟩ := hA.castleK c hck
    exact ⟨gpres (sq 4 c.home) .king (.inl rfl) hct b4 (bne_iff_ne.mp n1) (bne_iff_ne.mp n2),
      gpres (sq 7 c.home) .rook (.inr rfl) hct b7 (bne_iff_ne.mp n3) (bne_iff_ne.mp n4)⟩
  · intro hQ
    rw [play_castleQ] at hQ
    obtain ⟨hx1, n4⟩ := (Bool.and_eq_true _ _).mp hQ
    obtain ⟨hx2, n3⟩ := (Bool.and_eq_true _ _).mp hx1
    obtain ⟨hx3, n2⟩ := (Bool.and_eq_true _ _).mp hx2
    obtain ⟨hcq, n1⟩ := (Bool.and_eq_true _ _).mp hx3
    have hct : isCastle p m = true → c ≠ p.turn := by
      intro hcas he
      subst he
      obtain ⟨hsrc, hpn, hbK, hbd, hrto, hrfr, hside⟩ := castle_geom hmem hcas
      rw [hsrc] at n1
      simp at n1
    obtain ⟨b4, b0⟩ := hA.castleQ c hcq
    exact ⟨gpres (sq 4 c.home) .king (.inl rfl) hct b4 (bne_iff_ne.mp n1) (bne_iff_ne.mp n2),
      gpres (sq 0 c.home) .rook (.inr rfl) hct b0 (bne_iff_ne.mp n3) (bne_iff_ne.mp n4)⟩

theorem play_epOk {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ legalMoves p) :
    ∀ t, (play p m).ep = some t → EpOk (play p m) t := by
  obtain ⟨hmem, _⟩ := mem_legalMoves h
  intro t ht
  rw [play_ep] at ht
  split at ht
  · rename_i hd
    simp only [Option.some.injEq] at ht
    subst ht
    obtain ⟨h0, h1, h2, h3, h4⟩ := pseudo_double hmem hd
    have hsp : p.board m.src = some ⟨p.turn, .pawn⟩ := by
      unfold isDouble at hd
      obtain ⟨hb1, _⟩ := (Bool.and_eq_true _ _).mp hd
      obtain ⟨q, hbq, hcol⟩ := pseudo_src hmem
      obtain ⟨qc, qk⟩ := q
      rw [hbq, Option.any_some, beq_iff_eq] at hb1
      have hcol' : qc = p.turn := hcol
      rw [hbq, hcol']
      exact congrArg some (congrArg (Piece.mk p.turn) hb1)
    have hsd := pseudo_src_ne_dst hmem
    have hcf : isCastle p m = false := by
      have g : (p.board m.src).any (·.kind == .king) = false := by rw [hsp]; rfl
      unfold isCastle
      rw [g, Bool.false_and]
    have hff : (m.src.file != m.dst.file) = false := by
      rw [show m.src.file = m.dst.file from h1.symm]
      simp
    have hef : isEp p m = false := by
      unfold isEp
      rw [hff, Bool.and_false, Bool.false_and]
    have hpn : m.promo = none := by
      cases hp : m.promo with
      | none => rfl
      | some k =>
        exfalso
        obtain ⟨_, hlast, _, _⟩ := pseudo_promo hmem k hp
        rcases color_cases p.turn with ⟨hT, hfw, hph, hl, _, _⟩ | ⟨hT, hfw, hph, hl, _, _⟩
          <;> rw [hph] at h0 <;> rw [hfw] at h2 <;> rw [hl] at hlast <;> omega
    have hbeq := play_board_simple p m hcf hef
    have hmid8 : (m.src.rank + m.dst.rank) / 2 < 8 := by
      have h8a := rank_lt m.src
      have h8b := rank_lt m.dst
      omega
    have htm : (sq m.src.file ((m.src.rank + m.dst.rank) / 2)).file = m.src.file :=
      sq_file _ _ (file_lt _) hmid8
    have htr : (sq m.src.file ((m.src.rank + m.dst.rank) / 2)).rank =
        (m.src.rank + m.dst.rank) / 2 := sq_rank _ _ (file_lt _) hmid8
    rcases color_cases p.turn with ⟨hT, hfw, hph, hl, _, _⟩ | ⟨hT, hfw, hph, hl, _, _⟩
    · have hsr1 : m.src.rank = 1 := by rw [hph] at h0; exact h0
      have hdr3 : m.dst.rank = 3 := by rw [hfw] at h2; rw [hsr1] at h2; omega
      have hmid2 : (m.src.rank + m.dst.rank) / 2 = 2 := by rw [hsr1, hdr3]
      have hturn : (play p m).turn = .black := by rw [play_turn, hT]; rfl
      have h1517 : sq (sq m.src.file ((m.src.rank + m.dst.rank) / 2)).file 3 = m.dst := by
        apply sq_ext
        · rw [sq_file _ _ (file_lt _) (by decide), htm]
          exact h1.symm
        · rw [sq_rank _ _ (file_lt _) (by decide)]
          exact hdr3.symm
      have h1518 : sq (sq m.src.file ((m.src.rank + m.dst.rank) / 2)).file 1 = m.src := by
        apply sq_ext
        · rw [sq_file _ _ (file_lt _) (by decide), htm]
        · rw [sq_rank _ _ (file_lt _) (by decide)]
          exact hsr1.symm
      have hne1 : sq m.src.file ((m.src.rank + m.dst.rank) / 2) ≠ m.dst :=
        sq_ne_rank (by rw [htr, hmid2, hdr3]; decide)
      have hne2 : sq m.src.file ((m.src.rank + m.dst.rank) / 2) ≠ m.src :=
        sq_ne_rank (by rw [htr, hmid2, hsr1]; decide)
      unfold EpOk
      rw [hturn]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [htr, hmid2]
      · rw [h1517, hbeq, if_pos rfl, moved_of_no_promo hpn, hsp, hT]
      · rw [hbeq, if_neg hne1, if_neg hne2]
        exact h4
      · rw [h1518, hbeq, if_neg hsd, if_pos rfl]
    · have hsr6 : m.src.rank = 6 := by rw [hph] at h0; exact h0
      have hdr4 : m.dst.rank = 4 := by rw [hfw] at h2; rw [hsr6] at h2; omega
      have hmid5 : (m.src.rank + m.dst.rank) / 2 = 5 := by rw [hsr6, hdr4]
      have hturn : (play p m).turn = .white := by rw [play_turn, hT]; rfl
      have hdsteq : sq (sq m.src.file ((m.src.rank + m.dst.rank) / 2)).file 4 = m.dst := by
        apply sq_ext
        · rw [sq_file _ _ (file_lt _) (by decide), htm]
          exact h1.symm
        · rw [sq_rank _ _ (file_lt _) (by decide)]
          exact hdr4.symm
      have hsrceq : sq (sq m.src.file ((m.src.rank + m.dst.rank) / 2)).file 6 = m.src := by
        apply sq_ext
        · rw [sq_file _ _ (file_lt _) (by decide), htm]
        · rw [sq_rank _ _ (file_lt _) (by decide)]
          exact hsr6.symm
      have hne1 : sq m.src.file ((m.src.rank + m.dst.rank) / 2) ≠ m.dst :=
        sq_ne_rank (by rw [htr, hmid5, hdr4]; decide)
      have hne2 : sq m.src.file ((m.src.rank + m.dst.rank) / 2) ≠ m.src :=
        sq_ne_rank (by rw [htr, hmid5, hsr6]; decide)
      unfold EpOk
      rw [hturn]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [htr, hmid5]
      · rw [hdsteq, hbeq, if_pos rfl, moved_of_no_promo hpn, hsp, hT]
      · rw [hbeq, if_neg hne1, if_neg hne2]
        exact h4
      · rw [hsrceq, hbeq, if_neg hsd, if_pos rfl]
  · simp at ht

theorem play_material_mover {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ legalMoves p) :
    excess (play p m).board p.turn ≤ excess p.board p.turn := by
  obtain ⟨hmem, _⟩ := mem_legalMoves h
  have hsd := pseudo_src_ne_dst hmem
  by_cases hp : m.promo = none
  · by_cases hcas : isCastle p m = true
    · obtain ⟨hsrc2, hpn2, hbK, hbd, hrto, hrfr, hside⟩ := castle_geom hmem hcas
      obtain ⟨hds', hdt, hdf, hst, hsf, htf⟩ := castle_ne hmem hcas
      have hkn (k : Kind) : cnt (play p m).board p.turn k = cnt p.board p.turn k := by
        have e := cnt_play_castle p m hcas hds' hdt hdf hst hsf htf p.turn k
        rw [moved_of_no_promo hp, hbd, hrto, nbeq] at e
        simp only [bt_false] at e
        omega
      have hbn (par : Nat) : cntB (play p m).board p.turn par = cntB p.board p.turn par := by
        have e := cntB_play_castle p m hcas hds' hdt hdf hst hsf htf p.turn par
        rw [moved_of_no_promo hp, hbK, beq_kind_ne p.turn .king .bishop (by decide), hbd, hrto, nbeq,
          hrfr, beq_kind_ne p.turn .rook .bishop (by decide)] at e
        simp only [Bool.false_and, bt_false] at e
        omega
      have e1 := hkn .pawn; have e2 := hkn .knight; have e3 := hkn .rook; have e4 := hkn .queen
      have e5 := hbn 0; have e6 := hbn 1
      unfold excess
      omega
    · have hcf : isCastle p m = false := by
        cases h2 : isCastle p m with
        | false => rfl
        | true => exact absurd h2 hcas
      by_cases hep : isEp p m = true
      · obtain ⟨h1, h2, h3⟩ := ep_ne hmem hep
        have hspo := ep_pawn_src hmem hep
        obtain ⟨_, hvic, _, _⟩ := pseudo_ep hA hmem hep
        have hkn (k : Kind) : cnt (play p m).board p.turn k = cnt p.board p.turn k := by
          have e := cnt_play_ep p m hep h1 h2 h3 p.turn k
          rw [moved_of_no_promo hp, board_dst_ne hmem k, hvic,
            beq_color_ne p.turn.opp p.turn .pawn k (opp_ne_self _)] at e
          simp only [bt_false] at e
          omega
        have hbn (par : Nat) : cntB (play p m).board p.turn par = cntB p.board p.turn par := by
          have e := cntB_play_ep p m hep h1 h2 h3 p.turn par
          rw [moved_of_no_promo hp, hspo, beq_kind_ne p.turn .pawn .bishop (by decide),
            board_dst_ne hmem .bishop, hvic,
            beq_color_ne p.turn.opp p.turn .pawn .bishop (opp_ne_self _)] at e
          simp only [Bool.false_and, bt_false] at e
          omega
        have e1 := hkn .pawn; have e2 := hkn .knight; have e3 := hkn .rook; have e4 := hkn .queen
        have e5 := hbn 0; have e6 := hbn 1
        unfold excess
        omega
      · have hef2 : isEp p m = false := by
          cases h2 : isEp p m with
          | false => rfl
          | true => exact absurd h2 hep
        have hkn (k : Kind) : cnt (play p m).board p.turn k = cnt p.board p.turn k := by
          have e := cnt_play_simple p m hcf hef2 hsd p.turn k
          rw [moved_of_no_promo hp, board_dst_ne hmem k] at e
          simp only [bt_false] at e
          omega
        have hbn (par : Nat) : cntB (play p m).board p.turn par = cntB p.board p.turn par := by
          have e := cntB_play_simple p m hcf hef2 hsd p.turn par
          rw [bishop_indicator_no_promo hmem hp par, board_dst_ne hmem .bishop] at e
          simp only [Bool.false_and, bt_false] at e
          omega
        have e1 := hkn .pawn; have e2 := hkn .knight; have e3 := hkn .rook; have e4 := hkn .queen
        have e5 := hbn 0; have e6 := hbn 1
        unfold excess
        omega
  · cases hp2 : m.promo with
    | none => exact absurd hp2 hp
    | some k =>
      obtain ⟨hbs, hlast, hkp, hkk⟩ := pseudo_promo hmem k hp2
      have hmov : moved p m = some ⟨p.turn, k⟩ := by
        rw [moved_of_promo hp2, hbs]
        rfl
      have hcf : isCastle p m = false := by
        cases h2 : isCastle p m with
        | false => rfl
        | true =>
          obtain ⟨_, hpn2, _, _, _, _, _⟩ := castle_geom hmem h2
          rw [hpn2] at hp2
          simp at hp2
      have hef : isEp p m = false := by
        cases h2 : isEp p m with
        | false => rfl
        | true =>
          obtain ⟨_, _, hpn2, _⟩ := pseudo_ep hA hmem h2
          rw [hpn2] at hp2
          simp at hp2
      have hbb : ((some ⟨p.turn, .bishop⟩ : Option Piece) == some ⟨p.turn, .bishop⟩) = true :=
        beq_iff_eq.mpr rfl
      have hsrck : ((some ⟨p.turn, .pawn⟩ : Option Piece) == some ⟨p.turn, .pawn⟩) = true :=
        beq_iff_eq.mpr rfl
      have hp' : cnt (play p m).board p.turn .pawn + 1 = cnt p.board p.turn .pawn := by
        have e := cnt_play_simple p m hcf hef hsd p.turn .pawn
        rw [hmov, hbs, hsrck, beq_kind_ne p.turn k .pawn hkp, board_dst_ne hmem .pawn] at e
        simp only [bt_true, bt_false] at e
        omega
      have hk' : cnt (play p m).board p.turn k ≤ cnt p.board p.turn k + 1 := by
        have e := cnt_play_simple p m hcf hef hsd p.turn k
        have hself : ((some ⟨p.turn, k⟩ : Option Piece) == some ⟨p.turn, k⟩) = true :=
          beq_iff_eq.mpr rfl
        rw [hmov, hself, board_dst_ne hmem k] at e
        simp only [bt_true, bt_false] at e
        omega
      have ho' (k' : Kind) (hk1 : k' ≠ k) (hk2 : k' ≠ .pawn) :
          cnt (play p m).board p.turn k' ≤ cnt p.board p.turn k' := by
        have e := cnt_play_simple p m hcf hef hsd p.turn k'
        rw [hmov, hbs, beq_kind_ne p.turn k k' (fun hh => hk1 hh.symm),
          beq_kind_ne p.turn .pawn k' (fun hh => hk2 hh.symm), board_dst_ne hmem k'] at e
        simp only [bt_false] at e
        omega
      have hb' (par : Nat) : cntB (play p m).board p.turn par ≤
          cntB p.board p.turn par + (if k = .bishop then 1 else 0) := by
        have e := cntB_play_simple p m hcf hef hsd p.turn par
        rw [hmov, hbs, beq_kind_ne p.turn .pawn .bishop (by decide), board_dst_ne hmem .bishop] at e
        simp only [Bool.false_and, bt_false] at e
        have hbnd : ((some ⟨p.turn, k⟩ : Option Piece) == some ⟨p.turn, .bishop⟩).toNat ≤
            (if k = .bishop then 1 else 0) := by
          by_cases hkb : k = Kind.bishop
          · rw [if_pos hkb, hkb, hbb]
            decide
          · rw [if_neg hkb, show ((some ⟨p.turn, k⟩ : Option Piece) == some ⟨p.turn, .bishop⟩) =
                false from beq_kind_ne p.turn k .bishop hkb]
            decide
        have hand : ∀ x y : Bool, (x && y).toNat ≤ x.toNat := by
          intro x y
          cases x <;> cases y <;> decide
        have h1 := hand ((some ⟨p.turn, k⟩ : Option Piece) == some ⟨p.turn, .bishop⟩)
          (parity m.dst == par)
        omega
      have hb1 : k = .bishop →
          cntB (play p m).board p.turn 0 + cntB (play p m).board p.turn 1 ≤
            cntB p.board p.turn 0 + cntB p.board p.turn 1 + 1 := by
        intro hkb
        have e0 := cntB_play_simple p m hcf hef hsd p.turn 0
        have e1 := cntB_play_simple p m hcf hef hsd p.turn 1
        rw [hmov, hbs, beq_kind_ne p.turn .pawn .bishop (by decide), board_dst_ne hmem .bishop] at e0
        rw [hmov, hbs, beq_kind_ne p.turn .pawn .bishop (by decide), board_dst_ne hmem .bishop] at e1
        rw [hkb] at e0 e1
        rw [hbb] at e0 e1
        simp only [Bool.true_and, Bool.false_and, bt_true, bt_false] at e0 e1
        have hpd : parity m.dst < 2 := Nat.mod_lt _ (by decide)
        have f0 : (parity m.dst == 0).toNat + (parity m.dst == 1).toNat ≤ 1 := by
          rcases (by omega : parity m.dst = 0 ∨ parity m.dst = 1) with h0' | h1'
          · rw [h0']
            decide
          · rw [h1']
            decide
        omega
      exact excess_promo p.board (play p m).board p.turn k hp' hk' ho' hb' hb1

theorem admissible_play {p : Pos} {m : Move} (hA : Admissible p) (h : m ∈ legalMoves p) :
    Admissible (play p m) := by
  have hk := play_kings hA h
  have hs := play_safe h
  have hc := play_castle_rights hA h
  exact {
    kings := hk
    apart := apart_of_safe _ hk hs
    noBackPawn := play_noBackPawn hA h
    safe := hs
    menLe := fun c => Nat.le_trans (play_men hA h c) (hA.menLe c)
    material := fun c => by
      cases c <;> cases hp : p.turn
      all_goals first
        | exact Nat.le_trans (hp ▸ play_material_mover hA h) (hA.material _)
        | exact Nat.le_trans (by simpa [hp, Color.opp] using play_material_other hA h) (hA.material _)
    castleK := fun c => (hc c).1
    castleQ := fun c => (hc c).2
    ep := play_epOk hA h }

theorem reachable_admissible {p : Pos} (h : Reachable p) : Admissible p := by
  induction h with
  | init => exact admissible_initial
  | step _ hm ih => exact admissible_play ih hm

end Chess.All63
