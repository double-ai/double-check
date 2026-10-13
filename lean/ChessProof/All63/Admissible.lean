import ChessProof.Spec

namespace Chess.All63

def countSq (b : Board) (P : Option Piece → Bool) : Nat := (allSq.filter fun s => P (b s)).length

def cnt (b : Board) (c : Color) (k : Kind) : Nat := countSq b (· == some ⟨c, k⟩)

def parity (s : Sq) : Nat := (s.file + s.rank) % 2

def cntB (b : Board) (c : Color) (par : Nat) : Nat :=
  (allSq.filter fun s => b s == some ⟨c, .bishop⟩ && parity s == par).length

def men (b : Board) (c : Color) : Nat := countSq b fun o => o.any (·.color == c)

def excess (b : Board) (c : Color) : Nat :=
  cnt b c .pawn + (cnt b c .knight - 2) + (cnt b c .rook - 2) + (cnt b c .queen - 1) +
    (cntB b c 0 - 1) + (cntB b c 1 - 1)

def kingSq (p : Pos) (c : Color) : Sq := (allSq.find? fun s => p.board s == some ⟨c, .king⟩).getD 0

def dist (a b : Sq) : Nat := max ((a.file : Int) - b.file).natAbs ((a.rank : Int) - b.rank).natAbs

def EpOk (p : Pos) (t : Sq) : Prop :=
  match p.turn with
  | .white => t.rank = 5 ∧ p.board (sq t.file 4) = some ⟨.black, .pawn⟩ ∧ p.board t = none ∧
      p.board (sq t.file 6) = none
  | .black => t.rank = 2 ∧ p.board (sq t.file 3) = some ⟨.white, .pawn⟩ ∧ p.board t = none ∧
      p.board (sq t.file 1) = none

structure Admissible (p : Pos) : Prop where
  kings : ∀ c, cnt p.board c .king = 1
  apart : 1 < dist (kingSq p .white) (kingSq p .black)
  noBackPawn : ∀ s : Sq, ∀ c, (s.rank = 0 ∨ s.rank = 7) → p.board s ≠ some ⟨c, .pawn⟩
  safe : inCheck p p.turn.opp = false
  menLe : ∀ c, men p.board c ≤ 16
  material : ∀ c, excess p.board c ≤ 8
  castleK : ∀ c, p.castleK c = true →
    p.board (sq 4 c.home) = some ⟨c, .king⟩ ∧ p.board (sq 7 c.home) = some ⟨c, .rook⟩
  castleQ : ∀ c, p.castleQ c = true →
    p.board (sq 4 c.home) = some ⟨c, .king⟩ ∧ p.board (sq 0 c.home) = some ⟨c, .rook⟩
  ep : ∀ t, p.ep = some t → EpOk p t

def epOkB (p : Pos) (t : Sq) : Bool :=
  match p.turn with
  | .white => t.rank == 5 && p.board (sq t.file 4) == some ⟨.black, .pawn⟩ && p.board t == none &&
      p.board (sq t.file 6) == none
  | .black => t.rank == 2 && p.board (sq t.file 3) == some ⟨.white, .pawn⟩ && p.board t == none &&
      p.board (sq t.file 1) == none

def admB (p : Pos) : Bool :=
  [Color.white, .black].all (fun c =>
    cnt p.board c .king == 1 && men p.board c ≤ 16 && excess p.board c ≤ 8 &&
    (!p.castleK c || (p.board (sq 4 c.home) == some ⟨c, .king⟩ && p.board (sq 7 c.home) == some ⟨c, .rook⟩)) &&
    (!p.castleQ c || (p.board (sq 4 c.home) == some ⟨c, .king⟩ && p.board (sq 0 c.home) == some ⟨c, .rook⟩)) &&
    allSq.all fun s => !((s.rank == 0 || s.rank == 7) && p.board s == some ⟨c, .pawn⟩)) &&
  1 < dist (kingSq p .white) (kingSq p .black) &&
  !inCheck p p.turn.opp &&
  (match p.ep with
   | some t => epOkB p t
   | none => true)

theorem epOkB_iff (p : Pos) (t : Sq) : epOkB p t = true ↔ EpOk p t := by
  simp only [epOkB, EpOk]
  cases h : p.turn <;>
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem admB_iff (p : Pos) : admB p = true ↔ Admissible p := by
  constructor
  · intro h
    unfold admB at h
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    have hall := h.1.1.1
    have hapart' := h.1.1.2
    have hsafe' := h.1.2
    have hep := h.2
    rw [List.all_eq_true] at hall
    rw [decide_eq_true_eq] at hapart'
    rw [Bool.not_eq_true'] at hsafe'
    have colorMem (c : Color) : c ∈ [Color.white, Color.black] := by
      cases c <;> simp
    have parts (c : Color) : cnt p.board c .king = 1 ∧ men p.board c ≤ 16 ∧ excess p.board c ≤ 8 ∧
        (p.castleK c = true → p.board (sq 4 c.home) = some ⟨c, .king⟩ ∧
          p.board (sq 7 c.home) = some ⟨c, .rook⟩) ∧
        (p.castleQ c = true → p.board (sq 4 c.home) = some ⟨c, .king⟩ ∧
          p.board (sq 0 c.home) = some ⟨c, .rook⟩) ∧
        ∀ s : Sq, (s.rank = 0 ∨ s.rank = 7) → p.board s ≠ some ⟨c, .pawn⟩ := by
      have g := hall c (colorMem c)
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
        Bool.not_eq_true', List.all_eq_true] at g
      refine ⟨g.1.1.1.1.1, g.1.1.1.1.2, g.1.1.1.2, fun hk => ?_, fun hq => ?_, fun s hr hb2 => ?_⟩
      · exact (g.1.1.2).elim (fun hb => absurd (hb ▸ hk) (by decide)) (fun gx => gx)
      · exact (g.1.2).elim (fun hb => absurd (hb ▸ hq) (by decide)) (fun gx => gx)
      · have g' := g.2 s (List.mem_finRange s)
        have ht : ((s.rank == 0 || s.rank == 7) && p.board s == some ⟨c, .pawn⟩) = true := by
          rw [Bool.and_eq_true, Bool.or_eq_true]
          exact ⟨hr.elim (fun h => .inl (beq_iff_eq.mpr h)) (fun h => .inr (beq_iff_eq.mpr h)),
            beq_iff_eq.mpr hb2⟩
        rw [ht] at g'
        exact absurd g' (by decide)
    exact ⟨fun c => (parts c).1, hapart',
      fun s c hr hb2 => (parts c).2.2.2.2.2 s hr hb2,
      hsafe', fun c => (parts c).2.1, fun c => (parts c).2.2.1,
      fun c => (parts c).2.2.2.1, fun c => (parts c).2.2.2.2.1,
      fun t ht => by rw [ht] at hep; exact (epOkB_iff p t).mp hep⟩
  · rintro ⟨kings, apart, noBackPawn, safe, menLe, material, castleK, castleQ, ep⟩
    unfold admB
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [List.all_eq_true]
      intro c _
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact beq_iff_eq.mpr (kings c)
      · rw [decide_eq_true_eq]; exact menLe c
      · rw [decide_eq_true_eq]; exact material c
      · generalize hk : p.castleK c = bK
        have hk' := castleK c
        cases bK with
        | false => rw [Bool.or_eq_true]; exact .inl rfl
        | true =>
          obtain ⟨h4, h7⟩ := hk' hk
          rw [Bool.or_eq_true, Bool.and_eq_true]
          exact .inr ⟨beq_iff_eq.mpr h4, beq_iff_eq.mpr h7⟩
      · generalize hq : p.castleQ c = bQ
        have hq' := castleQ c
        cases bQ with
        | false => rw [Bool.or_eq_true]; exact .inl rfl
        | true =>
          obtain ⟨h4, h0⟩ := hq' hq
          rw [Bool.or_eq_true, Bool.and_eq_true]
          exact .inr ⟨beq_iff_eq.mpr h4, beq_iff_eq.mpr h0⟩
      · rw [List.all_eq_true]
        intro s _
        cases hbad : ((s.rank == 0 || s.rank == 7) && p.board s == some ⟨c, .pawn⟩) with
        | true =>
          rw [Bool.and_eq_true, Bool.or_eq_true] at hbad
          exact absurd (beq_iff_eq.mp hbad.2)
            (noBackPawn s c
              (hbad.1.elim (fun h => .inl (beq_iff_eq.mp h)) (fun h => .inr (beq_iff_eq.mp h))))
        | false => rfl
    · rw [decide_eq_true_eq]; exact apart
    · rw [Bool.not_eq_true']; exact safe
    · cases hep : p.ep with
      | none => rfl
      | some t => exact (epOkB_iff p t).mpr (ep t hep)

theorem find?_eq_of_filter {α : Type} (p : α → Bool) (l : List α) (x : α)
    (h : l.filter p = [x]) : l.find? p = some x := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : p a
    · rw [List.filter_cons_of_pos ha] at h
      injection h with hax _
      subst hax
      exact List.find?_cons_of_pos ha
    · rw [List.filter_cons_of_neg ha] at h
      rw [List.find?_cons_of_neg ha]
      exact ih h

theorem kingSq_spec (p : Pos) (c : Color) (h : cnt p.board c .king = 1) :
    p.board (kingSq p c) = some ⟨c, .king⟩ ∧ ∀ s, p.board s = some ⟨c, .king⟩ → s = kingSq p c := by
  simp only [cnt, countSq] at h
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h
  have hf : allSq.find? (fun s => p.board s == some ⟨c, .king⟩) = some x :=
    find?_eq_of_filter _ _ _ hx
  have hk : kingSq p c = x := by
    simp only [kingSq, hf, Option.getD_some]
  have hbx : p.board x = some ⟨c, .king⟩ := by
    have hm : x ∈ allSq.filter (fun s => p.board s == some ⟨c, .king⟩) := by
      rw [hx]; exact List.mem_cons_self
    rw [List.mem_filter] at hm
    exact beq_iff_eq.mp hm.2
  subst hk
  refine ⟨hbx, fun s hs => ?_⟩
  have hm : s ∈ allSq.filter (fun s => p.board s == some ⟨c, .king⟩) :=
    List.mem_filter.mpr ⟨List.mem_finRange s, beq_iff_eq.mpr hs⟩
  rw [hx] at hm
  exact List.mem_singleton.mp hm

theorem inCheck_iff_attacked (p : Pos) (c : Color) (h : cnt p.board c .king = 1) :
    inCheck p c = attacked p.board (kingSq p c) c.opp := by
  obtain ⟨hb, huniq⟩ := kingSq_spec p c h
  unfold inCheck
  rw [Bool.eq_iff_iff]
  constructor
  · intro hc
    rw [List.any_eq_true] at hc
    obtain ⟨t, _, ht⟩ := hc
    rw [Bool.and_eq_true] at ht
    have : t = kingSq p c := huniq t (beq_iff_eq.mp ht.1)
    subst this
    exact ht.2
  · intro hatt
    rw [List.any_eq_true]
    exact ⟨kingSq p c, List.mem_finRange _,
      by rw [Bool.and_eq_true]; exact ⟨beq_iff_eq.mpr hb, hatt⟩⟩

theorem excess_mono (b b' : Board) (c : Color)
    (hk : ∀ k, cnt b' c k ≤ cnt b c k) (hb : ∀ par, cntB b' c par ≤ cntB b c par) :
    excess b' c ≤ excess b c := by
  unfold excess
  have := hk .pawn; have := hk .knight; have := hk .rook; have := hk .queen
  have := hb 0; have := hb 1
  omega

theorem excess_aux {ap ap' an an' ar ar' aq aq' ab0 ab0' ab1 ab1' : Nat} (dn dr dq d0 d1 : Nat)
    (hp : ap' + 1 = ap) (hn : an' ≤ an + dn) (hr : ar' ≤ ar + dr) (hq : aq' ≤ aq + dq)
    (hb0 : ab0' ≤ ab0 + d0) (hb1 : ab1' ≤ ab1 + d1) (htot : dn + dr + dq + d0 + d1 ≤ 1) :
    ap' + (an' - 2) + (ar' - 2) + (aq' - 1) + (ab0' - 1) + (ab1' - 1) ≤
      ap + (an - 2) + (ar - 2) + (aq - 1) + (ab0 - 1) + (ab1 - 1) := by
  omega

theorem excess_auxB {ap ap' an an' ar ar' aq aq' ab0 ab0' ab1 ab1' : Nat}
    (hp : ap' + 1 = ap) (hn : an' ≤ an) (hr : ar' ≤ ar) (hq : aq' ≤ aq)
    (hb0 : ab0' ≤ ab0 + 1) (hb1 : ab1' ≤ ab1 + 1)
    (hsum : ab0' + ab1' ≤ ab0 + ab1 + 1) :
    ap' + (an' - 2) + (ar' - 2) + (aq' - 1) + (ab0' - 1) + (ab1' - 1) ≤
      ap + (an - 2) + (ar - 2) + (aq - 1) + (ab0 - 1) + (ab1 - 1) := by
  omega

theorem excess_promo (b b' : Board) (c : Color) (k : Kind)
    (hp : cnt b' c .pawn + 1 = cnt b c .pawn) (hk : cnt b' c k ≤ cnt b c k + 1)
    (ho : ∀ k', k' ≠ k → k' ≠ .pawn → cnt b' c k' ≤ cnt b c k')
    (hb : ∀ par, cntB b' c par ≤ cntB b c par + (if k = .bishop then 1 else 0))
    (hb1 : k = .bishop → cntB b' c 0 + cntB b' c 1 ≤ cntB b c 0 + cntB b c 1 + 1) :
    excess b' c ≤ excess b c := by
  unfold excess
  cases k with
  | pawn =>
    exact excess_aux 0 0 0 (if Kind.pawn = .bishop then 1 else 0)
      (if Kind.pawn = .bishop then 1 else 0) hp
      (ho .knight (by decide) (by decide)) (ho .rook (by decide) (by decide))
      (ho .queen (by decide) (by decide)) (hb 0) (hb 1) (by decide)
  | knight =>
    exact excess_aux 1 0 0 (if Kind.knight = .bishop then 1 else 0)
      (if Kind.knight = .bishop then 1 else 0) hp hk
      (ho .rook (by decide) (by decide)) (ho .queen (by decide) (by decide)) (hb 0) (hb 1) (by decide)
  | bishop =>
    exact excess_auxB hp (ho .knight (by decide) (by decide))
      (ho .rook (by decide) (by decide)) (ho .queen (by decide) (by decide)) (hb 0) (hb 1) (hb1 rfl)
  | rook =>
    exact excess_aux 0 1 0 (if Kind.rook = .bishop then 1 else 0)
      (if Kind.rook = .bishop then 1 else 0) hp
      (ho .knight (by decide) (by decide)) hk (ho .queen (by decide) (by decide)) (hb 0) (hb 1)
      (by decide)
  | queen =>
    exact excess_aux 0 0 1 (if Kind.queen = .bishop then 1 else 0)
      (if Kind.queen = .bishop then 1 else 0) hp
      (ho .knight (by decide) (by decide)) (ho .rook (by decide) (by decide)) hk (hb 0) (hb 1)
      (by decide)
  | king =>
    exact excess_aux 0 0 0 (if Kind.king = .bishop then 1 else 0)
      (if Kind.king = .bishop then 1 else 0) hp
      (ho .knight (by decide) (by decide)) (ho .rook (by decide) (by decide))
      (ho .queen (by decide) (by decide)) (hb 0) (hb 1) (by decide)

end Chess.All63
