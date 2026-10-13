import ChessProof.Spec
import ChessProof.All63.Admissible

namespace Chess.All63

def flipSq (s : Sq) : Sq := ⟨s.val ^^^ 56, by have := s.isLt; exact Nat.xor_lt_two_pow (n := 6) this (by decide)⟩

def flipPiece (q : Piece) : Piece := ⟨q.color.opp, q.kind⟩

def flipBoard (b : Board) : Board := fun s => (b (flipSq s)).map flipPiece

def flipMove (m : Move) : Move := ⟨flipSq m.src, flipSq m.dst, m.promo⟩

def flipPos (p : Pos) : Pos where
  board := flipBoard p.board
  turn := p.turn.opp
  castleK c := p.castleK c.opp
  castleQ c := p.castleQ c.opp
  ep := p.ep.map flipSq

def AllCheck (p : Pos) : Prop := ∀ m ∈ legalMoves p, givesCheck p m = true

theorem flipSq_flipSq (s : Sq) : flipSq (flipSq s) = s := by
  apply Fin.ext
  show (s.val ^^^ 56) ^^^ 56 = s.val
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem flipSq_file (s : Sq) : (flipSq s).file = s.file := by
  show (s.val ^^^ 56) % 8 = s.val % 8
  have h : ∀ v, v < 64 → (v ^^^ 56) % 8 = v % 8 := by decide
  exact h s.val s.isLt

theorem flipSq_rank (s : Sq) : (flipSq s).rank = 7 - s.rank := by
  show (s.val ^^^ 56) / 8 = 7 - s.val / 8
  have h : ∀ v, v < 64 → (v ^^^ 56) / 8 = 7 - v / 8 := by decide
  exact h s.val s.isLt

theorem flipPiece_flipPiece (q : Piece) : flipPiece (flipPiece q) = q := by
  obtain ⟨c, k⟩ := q
  cases c <;> rfl

theorem flipBoard_flipBoard (b : Board) : flipBoard (flipBoard b) = b := by
  funext s
  show ((b (flipSq (flipSq s))).map flipPiece).map flipPiece = b s
  rw [flipSq_flipSq, Option.map_map]
  cases b s with
  | none => rfl
  | some q => exact congrArg some (flipPiece_flipPiece q)

theorem flipPos_flipPos (p : Pos) : flipPos (flipPos p) = p := by
  obtain ⟨b, t, ck, cq, e⟩ := p
  show Pos.mk (flipBoard (flipBoard b)) t.opp.opp (fun c => ck c.opp.opp) (fun c => cq c.opp.opp)
      ((e.map flipSq).map flipSq) = Pos.mk b t ck cq e
  rw [Pos.mk.injEq]
  refine ⟨flipBoard_flipBoard b, by cases t <;> rfl, by funext c; cases c <;> rfl,
    by funext c; cases c <;> rfl, ?_⟩
  cases e with
  | none => rfl
  | some s => exact congrArg some (flipSq_flipSq s)

theorem mkSq_flip (f r : Nat) (hr : r < 8) :
    mkSq f (7 - r) = (mkSq f r).map flipSq := by
  by_cases hf : f < 8
  · have h1 : r * 8 + f < 64 := by omega
    have h2 : (r * 8 + f) / 8 = r := by omega
    have h3 : (r * 8 + f) % 8 = f := by omega
    have hx : ∀ v, v < 64 → v ^^^ 56 = (7 - v / 8) * 8 + v % 8 := by decide
    have hr7 : 7 - r < 8 := by omega
    simp only [mkSq]
    rw [dif_pos ⟨hf, hr7⟩, dif_pos ⟨hf, hr⟩]
    apply congrArg some
    apply Fin.ext
    show (7 - r) * 8 + f = (r * 8 + f) ^^^ 56
    rw [hx _ h1, h2, h3]
  · simp only [mkSq]
    rw [dif_neg (by omega), dif_neg (by omega), Option.map_none]

theorem off_flip_aux (sf sr df dr : Int) :
    (if 0 ≤ sf + df ∧ 0 ≤ 7 - sr + -dr then mkSq (sf + df).toNat (7 - sr + -dr).toNat else none) =
    (if 0 ≤ sf + df ∧ 0 ≤ sr + dr then mkSq (sf + df).toNat (sr + dr).toNat else none).map flipSq := by
  by_cases hP : 0 ≤ sf + df
  · by_cases hQ : 0 ≤ sr + dr
    · by_cases hQ7 : sr + dr < 8
      · rw [if_pos ⟨hP, by omega⟩, if_pos ⟨hP, hQ⟩]
        have htr : (7 - sr + -dr).toNat = 7 - (sr + dr).toNat := by omega
        rw [htr]
        exact mkSq_flip _ _ (by omega)
      · rw [if_neg (by omega), if_pos ⟨hP, hQ⟩]
        simp only [mkSq]
        rw [dif_neg (by omega), Option.map_none]
    · rw [if_pos ⟨hP, by omega⟩, if_neg (by omega)]
      simp only [mkSq]
      rw [dif_neg (by omega)]
      rfl
  · rw [if_neg (by omega), if_neg (by omega), Option.map_none]

theorem off_flip (s : Sq) (df dr : Int) : off (flipSq s) df (-dr) = (off s df dr).map flipSq := by
  have hsr : s.rank < 8 := by
    have := s.isLt
    unfold Sq.rank
    omega
  have hcast : ((7 - s.rank : Nat) : Int) = 7 - (s.rank : Int) := by omega
  simp only [off, flipSq_file, flipSq_rank, hcast]
  exact off_flip_aux _ _ _ _

theorem empty_flip (b : Board) (t : Sq) : empty (flipBoard b) (flipSq t) = empty b t := by
  show Option.isNone ((b (flipSq (flipSq t))).map flipPiece) = Option.isNone (b t)
  rw [flipSq_flipSq]
  cases b t <;> rfl

theorem ray_flip (b : Board) (s : Sq) (df dr : Int) (n : Nat) :
    ray (flipBoard b) (flipSq s) df (-dr) n = (ray b s df dr n).map flipSq := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show (match off (flipSq s) df (-dr) with
      | none => []
      | some t => if empty (flipBoard b) t then t :: ray (flipBoard b) t df (-dr) n else [t])
        = (match off s df dr with
      | none => []
      | some t => if empty b t then t :: ray b t df dr n else [t]).map flipSq
    rw [off_flip]
    cases h : off s df dr with
    | none => rfl
    | some t =>
      show (if empty (flipBoard b) (flipSq t) then flipSq t :: ray (flipBoard b) (flipSq t) df (-dr) n
          else [flipSq t])
        = (if empty b t then t :: ray b t df dr n else [t]).map flipSq
      rw [empty_flip]
      by_cases he : empty b t
      · rw [if_pos he, if_pos he, ih t]
        rfl
      · rw [if_neg he, if_neg he]
        rfl

theorem opp_opp (c : Color) : c.opp.opp = c := by cases c <;> rfl

theorem opp_beq_opp (c₁ c₂ : Color) : (c₁.opp == c₂.opp) = (c₁ == c₂) := by
  cases c₁ <;> cases c₂ <;> rfl

theorem flipSq_injective : Function.Injective flipSq := by
  intro a b h
  have h2 := congrArg flipSq h
  rwa [flipSq_flipSq, flipSq_flipSq] at h2

theorem mem_flipSq_map {l : List Sq} {t : Sq} : flipSq t ∈ l.map flipSq ↔ t ∈ l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨u, hu, hu2⟩
    rwa [flipSq_injective hu2] at hu
  · intro h
    exact ⟨t, h, rfl⟩

theorem off_flip_eq (s t : Sq) (df dr : Int) :
    off (flipSq s) df dr = some (flipSq t) ↔ off s df (-dr) = some t := by
  have h := off_flip s df (-dr)
  rw [Int.neg_neg] at h
  rw [h, Option.map_eq_some_iff]
  constructor
  · rintro ⟨u, hu, hu2⟩
    rwa [flipSq_injective hu2] at hu
  · intro ht
    exact ⟨t, ht, rfl⟩

theorem mem_ray_flip (b : Board) (s t : Sq) (df dr : Int) (n : Nat) :
    flipSq t ∈ ray (flipBoard b) (flipSq s) df dr n ↔ t ∈ ray b s df (-dr) n := by
  have h := ray_flip b s df (-dr) n
  rw [Int.neg_neg] at h
  rw [h]
  exact mem_flipSq_map

theorem mem_steps_flip (s t : Sq) (ds : List (Int × Int)) :
    flipSq t ∈ steps (flipSq s) ds ↔ t ∈ steps s (ds.map fun d => (d.1, -d.2)) := by
  simp only [steps, List.mem_filterMap, List.mem_map]
  constructor
  · rintro ⟨d, hd, hoff⟩
    exact ⟨(d.1, -d.2), ⟨d, hd, rfl⟩, (off_flip_eq s t d.1 d.2).mp hoff⟩
  · rintro ⟨y, ⟨d, hd, rfl⟩, hoff⟩
    exact ⟨d, hd, (off_flip_eq s t d.1 d.2).mpr hoff⟩

theorem mem_rays_flip (b : Board) (s t : Sq) (ds : List (Int × Int)) :
    flipSq t ∈ rays (flipBoard b) (flipSq s) ds ↔ t ∈ rays b s (ds.map fun d => (d.1, -d.2)) := by
  simp only [rays, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨d, hd, hray⟩
    exact ⟨(d.1, -d.2), ⟨d, hd, rfl⟩, (mem_ray_flip b s t d.1 d.2 7).mp hray⟩
  · rintro ⟨y, ⟨d, hd, rfl⟩, hray⟩
    exact ⟨d, hd, (mem_ray_flip b s t d.1 d.2 7).mpr hray⟩

theorem mem_steps_of_perm {ds₁ ds₂ : List (Int × Int)} (h : List.Perm ds₁ ds₂) (s t : Sq) :
    t ∈ steps s ds₁ ↔ t ∈ steps s ds₂ := by
  simp only [steps, List.mem_filterMap]
  exact exists_congr fun d => and_congr h.mem_iff Iff.rfl

theorem mem_rays_of_perm {ds₁ ds₂ : List (Int × Int)} (h : List.Perm ds₁ ds₂) (b : Board) (s t : Sq) :
    t ∈ rays b s ds₁ ↔ t ∈ rays b s ds₂ := by
  simp only [rays, List.mem_flatMap]
  exact exists_congr fun d => and_congr h.mem_iff Iff.rfl

theorem knightD_neg_perm : List.Perm (knightD.map fun d => (d.1, -d.2)) knightD := by decide

theorem bishopD_neg_perm : List.Perm (bishopD.map fun d => (d.1, -d.2)) bishopD := by decide

theorem rookD_neg_perm : List.Perm (rookD.map fun d => (d.1, -d.2)) rookD := by decide

theorem queenD_neg_perm : List.Perm (queenD.map fun d => (d.1, -d.2)) queenD := by decide

theorem pawnD_neg_perm (c : Color) :
    List.Perm ([(1, c.opp.fwd), (-1, c.opp.fwd)].map fun d => (d.1, -d.2)) [(1, c.fwd), (-1, c.fwd)] := by
  cases c <;> decide

theorem mem_attacks_flip (b : Board) (s t : Sq) (q : Piece) :
    flipSq t ∈ attacks (flipBoard b) (flipSq s) (flipPiece q) ↔ t ∈ attacks b s q := by
  obtain ⟨c, k⟩ := q
  cases k
  case pawn =>
    show flipSq t ∈ steps (flipSq s) [(1, c.opp.fwd), (-1, c.opp.fwd)] ↔
      t ∈ steps s [(1, c.fwd), (-1, c.fwd)]
    exact (mem_steps_flip s t _).trans (mem_steps_of_perm (pawnD_neg_perm c) s t)
  case knight =>
    show flipSq t ∈ steps (flipSq s) knightD ↔ t ∈ steps s knightD
    exact (mem_steps_flip s t _).trans (mem_steps_of_perm knightD_neg_perm s t)
  case bishop =>
    show flipSq t ∈ rays (flipBoard b) (flipSq s) bishopD ↔ t ∈ rays b s bishopD
    exact (mem_rays_flip b s t _).trans (mem_rays_of_perm bishopD_neg_perm b s t)
  case rook =>
    show flipSq t ∈ rays (flipBoard b) (flipSq s) rookD ↔ t ∈ rays b s rookD
    exact (mem_rays_flip b s t _).trans (mem_rays_of_perm rookD_neg_perm b s t)
  case queen =>
    show flipSq t ∈ rays (flipBoard b) (flipSq s) queenD ↔ t ∈ rays b s queenD
    exact (mem_rays_flip b s t _).trans (mem_rays_of_perm queenD_neg_perm b s t)
  case king =>
    show flipSq t ∈ steps (flipSq s) queenD ↔ t ∈ steps s queenD
    exact (mem_steps_flip s t _).trans (mem_steps_of_perm queenD_neg_perm s t)

theorem attacked_flip_le (b : Board) (s : Sq) (c : Color) (h : attacked b s c = true) :
    attacked (flipBoard b) (flipSq s) c.opp = true := by
  unfold attacked at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨t, -, h⟩ := h
  refine ⟨flipSq t, List.mem_finRange _, ?_⟩
  have hb : flipBoard b (flipSq t) = (b t).map flipPiece := by
    show (b (flipSq (flipSq t))).map flipPiece = _
    rw [flipSq_flipSq]
  rw [hb]
  cases hbt : b t with
  | none =>
    rw [hbt] at h
    exact Bool.noConfusion h
  | some q =>
    rw [hbt] at h
    change (q.color == c && (attacks b t q).contains s) = true at h
    show ((flipPiece q).color == c.opp && (attacks (flipBoard b) (flipSq t) (flipPiece q)).contains (flipSq s)) = true
    rw [Bool.and_eq_true] at h ⊢
    obtain ⟨hc, ha⟩ := h
    constructor
    · show ((flipPiece q).color == c.opp) = true
      have hq : (flipPiece q).color = q.color.opp := rfl
      rw [hq, opp_beq_opp]
      exact hc
    · rw [List.contains_eq_mem]
      rw [List.contains_eq_mem] at ha
      exact decide_eq_true (mem_attacks_flip b t s q |>.mpr (of_decide_eq_true ha))

theorem attacked_flip (b : Board) (s : Sq) (c : Color) :
    attacked (flipBoard b) (flipSq s) c.opp = attacked b s c := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    have h2 := attacked_flip_le (flipBoard b) (flipSq s) c.opp h
    rwa [flipBoard_flipBoard, flipSq_flipSq, opp_opp] at h2
  · intro h
    exact attacked_flip_le b s c h

theorem inCheck_flip_le (p : Pos) (c : Color) (h : inCheck p c = true) :
    inCheck (flipPos p) c.opp = true := by
  unfold inCheck at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨t, -, h⟩ := h
  refine ⟨flipSq t, List.mem_finRange _, ?_⟩
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨hk, ha⟩ := h
  constructor
  · have hbt : p.board t = some ⟨c, .king⟩ := beq_iff_eq.mp hk
    have hb : (flipPos p).board (flipSq t) = (p.board t).map flipPiece := by
      show (p.board (flipSq (flipSq t))).map flipPiece = _
      rw [flipSq_flipSq]
    rw [hb, hbt]
    exact beq_iff_eq.mpr rfl
  · exact attacked_flip_le p.board t c.opp ha

theorem inCheck_flip (p : Pos) (c : Color) : inCheck (flipPos p) c.opp = inCheck p c := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    have h2 := inCheck_flip_le (flipPos p) c.opp h
    rwa [flipPos_flipPos, opp_opp] at h2
  · intro h
    exact inCheck_flip_le p c h

theorem off_some_sub (s t : Sq) (df dr : Int) (h : off s df dr = some t) :
    (t.file : Int) = s.file + df ∧ (t.rank : Int) = s.rank + dr := by
  have h2 : (if 0 ≤ (s.file : Int) + df ∧ 0 ≤ (s.rank : Int) + dr
      then mkSq ((s.file : Int) + df).toNat ((s.rank : Int) + dr).toNat else none) = some t := h
  split at h2
  · rename_i hh
    obtain ⟨hf, hr⟩ := hh
    unfold mkSq at h2
    split at h2
    · rename_i hb
      obtain ⟨hfl, hrl⟩ := hb
      obtain ⟨rfl⟩ := h2
      have hf8 : ((s.file : Int) + df).toNat < 8 := hfl
      have htof : ((s.file : Int) + df).toNat = s.file + df := Int.toNat_of_nonneg hf
      have htor : ((s.rank : Int) + dr).toNat = s.rank + dr := Int.toNat_of_nonneg hr
      constructor
      · show ((((((s.rank : Int) + dr).toNat * 8 + ((s.file : Int) + df).toNat)) % 8 : Nat) : Int) = _
        rw [show (((s.rank : Int) + dr).toNat * 8 + ((s.file : Int) + df).toNat) % 8 =
            ((s.file : Int) + df).toNat from by omega]
        exact htof
      · show ((((((s.rank : Int) + dr).toNat * 8 + ((s.file : Int) + df).toNat)) / 8 : Nat) : Int) = _
        rw [show (((s.rank : Int) + dr).toNat * 8 + ((s.file : Int) + df).toNat) / 8 =
            ((s.rank : Int) + dr).toNat from by omega]
        exact htor
    · simp at h2
  · simp at h2

theorem nodup_map_of_inj {α β : Type} {f : α → β} {l : List α} (hl : l.Nodup)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at hl
    refine ⟨?_, ih hl.2 (fun x hx y hy h => hinj x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy) h)⟩
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨y, hy, hy2⟩ := hm
    have : a = y := hinj a (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy) hy2.symm
    exact hl.1 (this ▸ hy)

theorem nodup_filterMap {α β : Type} {f : α → Option β} {l : List α} (hl : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, ∀ y, f a = some y → f b = some y → a = b) :
    (l.filterMap f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    cases hfa : f a with
    | none =>
      rw [List.filterMap_cons, hfa]
      exact ih (List.nodup_cons.mp hl).2 (fun x hx y hy₂ z h1 h2 =>
        hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy₂) z h1 h2)
    | some v =>
      rw [List.filterMap_cons, hfa, List.nodup_cons]
      rw [List.nodup_cons] at hl
      refine ⟨?_, ih hl.2 (fun x hx y hy₂ z h1 h2 =>
        hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy₂) z h1 h2)⟩
      intro hm
      rw [List.mem_filterMap] at hm
      obtain ⟨b, hb, hb2⟩ := hm
      have : a = b := hinj a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) _
        hfa hb2
      exact hl.1 (this ▸ hb)

theorem nodup_flatMap {α β : Type} {f : α → List β} {l : List α} (hl : l.Nodup)
    (hf : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ f a, ∀ y ∈ f b, x ≠ y) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    rw [List.flatMap_cons, List.nodup_append]
    rw [List.nodup_cons] at hl
    refine ⟨hf a (List.mem_cons_self ..),
      ih hl.2 (fun b hb => hf b (List.mem_cons_of_mem _ hb))
        (fun b hb c hc hbc => hdisj b (List.mem_cons_of_mem _ hb) c
          (List.mem_cons_of_mem _ hc) hbc), ?_⟩
    intro x hx y hy hxy
    rw [List.mem_flatMap] at hy
    obtain ⟨b, hb, hb2⟩ := hy
    exact hdisj a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb)
      (fun hab => hl.1 (hab ▸ hb)) x hx y hb2 hxy

theorem nodup_steps (s : Sq) (ds : List (Int × Int)) (hd : ds.Nodup) :
    (steps s ds).Nodup := by
  apply nodup_filterMap hd
  rintro ⟨df, dr⟩ - ⟨df', dr'⟩ - y h1 h2
  obtain ⟨e1, e2⟩ := off_some_sub s y df dr h1
  obtain ⟨e1', e2'⟩ := off_some_sub s y df' dr' h2
  have : df = df' ∧ dr = dr' := by omega
  rw [this.1, this.2]

theorem nodup_steps_filter (s : Sq) (ds : List (Int × Int)) (hd : ds.Nodup)
    (P : Sq → Bool) : ((steps s ds).filter P).Nodup :=
  List.Nodup.sublist List.filter_sublist (nodup_steps s ds hd)

theorem mem_ray_sub (b : Board) (s t : Sq) (df dr : Int) (n : Nat)
    (h : t ∈ ray b s df dr n) :
    ∃ j : Nat, 1 ≤ j ∧ (t.file : Int) - s.file = (j : Int) * df ∧
      (t.rank : Int) - s.rank = (j : Int) * dr := by
  induction n generalizing s with
  | zero => simp only [ray, List.not_mem_nil] at h
  | succ n ih =>
    have h2 : t ∈ (match off s df dr with
        | none => []
        | some u => if empty b u then u :: ray b u df dr n else [u]) := h
    split at h2
    · simp only [List.not_mem_nil] at h2
    · rename_i u hu
      split at h2
      · rename_i he
        rw [List.mem_cons] at h2
        rcases h2 with rfl | h2
        · obtain ⟨e1, e2⟩ := off_some_sub s t df dr hu
          exact ⟨1, Nat.le_refl 1, by omega, by omega⟩
        · obtain ⟨j, hj1, hjf, hjr⟩ := ih u h2
          obtain ⟨e1, e2⟩ := off_some_sub s u df dr hu
          have hc : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
          refine ⟨j + 1, by omega, ?_, ?_⟩
          · rw [hc, Int.add_mul, Int.one_mul]; omega
          · rw [hc, Int.add_mul, Int.one_mul]; omega
      · rw [List.mem_singleton] at h2
        subst h2
        obtain ⟨e1, e2⟩ := off_some_sub s t df dr hu
        exact ⟨1, Nat.le_refl 1, by omega, by omega⟩

theorem ray_nodup (b : Board) (s : Sq) (df dr : Int) (n : Nat)
    (hdir : df ≠ 0 ∨ dr ≠ 0) : (ray b s df dr n).Nodup := by
  induction n generalizing s with
  | zero => exact List.nodup_nil
  | succ n ih =>
    show (match off s df dr with
        | none => []
        | some u => if empty b u then u :: ray b u df dr n else [u]).Nodup
    split
    · exact List.nodup_nil
    · rename_i u hu
      split
      · rename_i he
        rw [List.nodup_cons]
        refine ⟨?_, ih u⟩
        intro hm
        obtain ⟨j, hj1, hjf, hjr⟩ := mem_ray_sub b u u df dr n hm
        have hjz : (j : Int) ≠ 0 := by omega
        rcases hdir with hdf | hdr
        · have hz : (j : Int) * df = 0 := by omega
          rcases Int.mul_eq_zero.mp hz with h1 | h1
          · exact absurd h1 hjz
          · exact hdf h1
        · have hz : (j : Int) * dr = 0 := by omega
          rcases Int.mul_eq_zero.mp hz with h1 | h1
          · exact absurd h1 hjz
          · exact hdr h1
      · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem nodup_rays (b : Board) (s : Sq) (ds : List (Int × Int)) (hd : ds.Nodup)
    (hne : ∀ df dr, (df, dr) ∈ ds → df ≠ 0 ∨ dr ≠ 0)
    (hdir : ∀ df₁ dr₁ df₂ dr₂, (df₁, dr₁) ∈ ds → (df₂, dr₂) ∈ ds →
      ∀ (j k : Nat), 1 ≤ j → 1 ≤ k →
        (j : Int) * df₁ = (k : Int) * df₂ → (j : Int) * dr₁ = (k : Int) * dr₂ →
        (df₁, dr₁) = (df₂, dr₂)) :
    (rays b s ds).Nodup := by
  apply nodup_flatMap hd
  · rintro ⟨df, dr⟩ hd'
    exact ray_nodup b s df dr 7 (hne df dr hd')
  · rintro ⟨df₁, dr₁⟩ h1 ⟨df₂, dr₂⟩ h2 hne12 x hx y hy rfl
    obtain ⟨j, hj1, hjf, hjr⟩ := mem_ray_sub b s x df₁ dr₁ 7 hx
    obtain ⟨k, hk1, hkf, hkr⟩ := mem_ray_sub b s x df₂ dr₂ 7 hy
    exact hne12 (hdir df₁ dr₁ df₂ dr₂ h1 h2 j k hj1 hk1 (by omega) (by omega))

theorem mem_dirs_ne {d : Int × Int} (h : d ∈ bishopD) : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
  simp only [bishopD, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem mem_dirs_ne_rook {d : Int × Int} (h : d ∈ rookD) : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
  simp only [rookD, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem rookD_nodup : rookD.Nodup := by decide

theorem bishopD_nodup : bishopD.Nodup := by decide

theorem queenD_nodup : queenD.Nodup := by decide

theorem knightD_nodup : knightD.Nodup := by decide

theorem dir_rook (df₁ dr₁ df₂ dr₂ : Int)
    (h1 : (df₁, dr₁) ∈ rookD) (h2 : (df₂, dr₂) ∈ rookD)
    (j k : Nat) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (e1 : (j : Int) * df₁ = (k : Int) * df₂) (e2 : (j : Int) * dr₁ = (k : Int) * dr₂) :
    (df₁, dr₁) = (df₂, dr₂) := by
  simp only [rookD, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    Prod.mk.injEq] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | rfl | (exfalso; omega)

theorem dir_bishop (df₁ dr₁ df₂ dr₂ : Int)
    (h1 : (df₁, dr₁) ∈ bishopD) (h2 : (df₂, dr₂) ∈ bishopD)
    (j k : Nat) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (e1 : (j : Int) * df₁ = (k : Int) * df₂) (e2 : (j : Int) * dr₁ = (k : Int) * dr₂) :
    (df₁, dr₁) = (df₂, dr₂) := by
  simp only [bishopD, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    Prod.mk.injEq] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | rfl | (exfalso; omega)

theorem dir_queen (df₁ dr₁ df₂ dr₂ : Int)
    (h1 : (df₁, dr₁) ∈ queenD) (h2 : (df₂, dr₂) ∈ queenD)
    (j k : Nat) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (e1 : (j : Int) * df₁ = (k : Int) * df₂) (e2 : (j : Int) * dr₁ = (k : Int) * dr₂) :
    (df₁, dr₁) = (df₂, dr₂) := by
  simp only [queenD, rookD, bishopD, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc, Prod.mk.injEq] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | rfl | (exfalso; omega)

theorem mem_dir_ne_queen {d : Int × Int} (h : d ∈ queenD) : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
  simp only [queenD, rookD, bishopD, List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, or_assoc] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem attacks_nodup (b : Board) (s : Sq) (q : Piece) : (attacks b s q).Nodup := by
  obtain ⟨c, k⟩ := q
  cases k
  case pawn =>
    show (steps s [(1, c.fwd), (-1, c.fwd)]).Nodup
    apply nodup_steps
    cases c <;> decide
  case knight => exact nodup_steps s knightD knightD_nodup
  case king => exact nodup_steps s queenD queenD_nodup
  case bishop =>
    exact nodup_rays b s bishopD bishopD_nodup (fun df dr h => mem_dirs_ne h)
      (fun _ _ _ _ h1 h2 => dir_bishop _ _ _ _ h1 h2)
  case rook =>
    exact nodup_rays b s rookD rookD_nodup (fun df dr h => mem_dirs_ne_rook h)
      (fun _ _ _ _ h1 h2 => dir_rook _ _ _ _ h1 h2)
  case queen =>
    exact nodup_rays b s queenD queenD_nodup (fun df dr h => mem_dir_ne_queen h)
      (fun _ _ _ _ h1 h2 => dir_queen _ _ _ _ h1 h2)

theorem nodup_toList {α : Type} (o : Option α) : o.toList.Nodup := by
  cases o with
  | none => exact List.nodup_nil
  | some a => exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem mem_of_filter_toList {α : Type} {o : Option α} {P : α → Bool} {t : α}
    (h : t ∈ (o.filter P).toList) : o = some t := by
  cases o with
  | none => exact False.elim (List.not_mem_nil h)
  | some a =>
    have h2 : t ∈ (if P a then some a else none).toList := h
    split at h2
    · rw [Option.mem_toList] at h2
      rw [Option.some.inj h2]
    · exact False.elim (List.not_mem_nil h2)

theorem file_sq (f r : Nat) (hf : f < 8) (hr : r < 8) : (sq f r).file = f := by
  show ((r * 8 + f) % 64) % 8 = f
  omega

theorem home_lt (c : Color) : c.home < 8 := by cases c <;> decide

theorem fwd_ne_zero (c : Color) : c.fwd = 1 ∨ c.fwd = -1 := by
  cases c with
  | white => exact Or.inl rfl
  | black => exact Or.inr rfl

theorem pawnMoves_eq (p : Pos) (s : Sq) (c : Color) :
    pawnMoves p s c =
      ((((off s 0 c.fwd).filter (empty p.board)).toList ++
        (steps s [(1, c.fwd), (-1, c.fwd)]).filter (fun t =>
          foe p.board c t || epCap p c t)).flatMap (fun t =>
        if t.rank == c.last then [Kind.knight, .bishop, .rook, .queen].map (fun k =>
          (⟨s, t, some k⟩ : Move))
        else [(⟨s, t, none⟩ : Move)])) ++
      (if s.rank == c.pawnHome && ((off s 0 c.fwd).filter (empty p.board)).isSome then
        (off s 0 (2 * c.fwd)).filter (empty p.board) else none).toList.map (fun t =>
        (⟨s, t, none⟩ : Move)) := rfl

theorem mem_mk_part {s t : Sq} {c : Color} {m : Move}
    (h : m ∈ (if t.rank == c.last then
        [Kind.knight, .bishop, .rook, .queen].map (fun k => (⟨s, t, some k⟩ : Move))
      else [(⟨s, t, none⟩ : Move)])) :
    m.dst = t ∧ m.src = s := by
  split at h
  · rw [List.mem_map] at h
    obtain ⟨k, -, hk⟩ := h
    rw [← hk]
    exact ⟨rfl, rfl⟩
  · rw [List.mem_singleton] at h
    rw [h]
    exact ⟨rfl, rfl⟩

theorem nodup_mk (s t : Sq) (c : Color) :
    (if t.rank == c.last then [Kind.knight, .bishop, .rook, .queen].map (fun k =>
        (⟨s, t, some k⟩ : Move))
      else [(⟨s, t, none⟩ : Move)]).Nodup := by
  split
  · apply nodup_map_of_inj
    · decide
    · intro x _ y _ hxy
      simp only [Move.mk.injEq] at hxy
      exact Option.some.inj hxy.2.2
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem capsD_nodup (c : Color) : [(1, c.fwd), (-1, c.fwd)].Nodup := by
  cases c <;> decide

theorem nodup_one_caps (p : Pos) (s : Sq) (c : Color) :
    (((off s 0 c.fwd).filter (empty p.board)).toList ++
      (steps s [(1, c.fwd), (-1, c.fwd)]).filter (fun t =>
        foe p.board c t || epCap p c t)).Nodup := by
  rw [List.nodup_append]
  refine ⟨nodup_toList _, nodup_steps_filter _ _ (capsD_nodup c) _, ?_⟩
  intro x hx y hy hxy
  have hox : off s 0 c.fwd = some x := mem_of_filter_toList hx
  obtain ⟨fx, -⟩ := off_some_sub s x 0 c.fwd hox
  have hyst : y ∈ steps s [(1, c.fwd), (-1, c.fwd)] := (List.mem_filter.mp hy).1
  rw [steps, List.mem_filterMap] at hyst
  obtain ⟨⟨df, dr⟩, hd, hoff⟩ := hyst
  obtain ⟨fyend, -⟩ := off_some_sub s y df dr hoff
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hd
  have hfx : (x.file : Int) = s.file := by omega
  have hfy : (y.file : Int) = s.file + 1 ∨ (y.file : Int) = s.file - 1 := by
    rcases hd with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
  have : (x.file : Int) = y.file := congrArg (fun v => (v.file : Int)) hxy
  omega

theorem rank_mem_one_caps {p : Pos} {s t : Sq} {c : Color}
    (h : t ∈ ((off s 0 c.fwd).filter (empty p.board)).toList ++
      (steps s [(1, c.fwd), (-1, c.fwd)]).filter (fun t =>
        foe p.board c t || epCap p c t)) :
    (t.rank : Int) = s.rank + c.fwd := by
  rw [List.mem_append] at h
  rcases h with h | h
  · have ho := mem_of_filter_toList h
    obtain ⟨-, fr⟩ := off_some_sub s t 0 c.fwd ho
    omega
  · have hst : t ∈ steps s [(1, c.fwd), (-1, c.fwd)] := (List.mem_filter.mp h).1
    rw [steps, List.mem_filterMap] at hst
    obtain ⟨⟨df, dr⟩, hd, hoff⟩ := hst
    obtain ⟨-, fr⟩ := off_some_sub s t df dr hoff
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hd
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem dst_mem_flatMap_mk {p : Pos} {s : Sq} {c : Color} {m : Move}
    (h : m ∈ ((((off s 0 c.fwd).filter (empty p.board)).toList ++
        (steps s [(1, c.fwd), (-1, c.fwd)]).filter (fun t =>
          foe p.board c t || epCap p c t)).flatMap (fun t =>
      if t.rank == c.last then [Kind.knight, .bishop, .rook, .queen].map (fun k =>
        (⟨s, t, some k⟩ : Move))
      else [(⟨s, t, none⟩ : Move)]))) :
    m.dst ∈ ((off s 0 c.fwd).filter (empty p.board)).toList ++
      (steps s [(1, c.fwd), (-1, c.fwd)]).filter (fun t =>
        foe p.board c t || epCap p c t) ∧ m.src = s := by
  rw [List.mem_flatMap] at h
  obtain ⟨t, ht, hmk⟩ := h
  obtain ⟨hd, hs⟩ := mem_mk_part hmk
  exact ⟨hd ▸ ht, hs⟩

theorem nodup_flatMap_mk (p : Pos) (s : Sq) (c : Color) :
    ((((off s 0 c.fwd).filter (empty p.board)).toList ++
        (steps s [(1, c.fwd), (-1, c.fwd)]).filter (fun t =>
          foe p.board c t || epCap p c t)).flatMap (fun t =>
      if t.rank == c.last then [Kind.knight, .bishop, .rook, .queen].map (fun k =>
        (⟨s, t, some k⟩ : Move))
      else [(⟨s, t, none⟩ : Move)])).Nodup := by
  apply nodup_flatMap (nodup_one_caps p s c)
  · intro t _
    exact nodup_mk s t c
  · intro t₁ _ t₂ _ ht12 x hx y hy hxy
    obtain ⟨hd1, -⟩ := mem_mk_part hx
    obtain ⟨hd2, -⟩ := mem_mk_part hy
    exact ht12 (hd1 ▸ hd2 ▸ congrArg Move.dst hxy)

theorem pawnMoves_nodup (p : Pos) (s : Sq) (c : Color) : (pawnMoves p s c).Nodup := by
  rw [pawnMoves_eq]
  split
  · rw [List.nodup_append]
    refine ⟨nodup_flatMap_mk p s c, nodup_map_of_inj (nodup_toList _) ?_, ?_⟩
    · intro x _ y _ hxy
      simp only [Move.mk.injEq] at hxy
      exact hxy.2.1
    · intro x hx y hy hxy
      obtain ⟨hdx, -⟩ := dst_mem_flatMap_mk hx
      have hr1 : (x.dst.rank : Int) = s.rank + c.fwd := rank_mem_one_caps hdx
      rw [List.mem_map] at hy
      obtain ⟨t₂, ht₂, hty⟩ := hy
      have h2 : (t₂.rank : Int) = s.rank + 2 * c.fwd := by
        have hoff : off s 0 (2 * c.fwd) = some t₂ := mem_of_filter_toList ht₂
        obtain ⟨-, fr⟩ := off_some_sub s t₂ 0 (2 * c.fwd) hoff
        omega
      have hd2 : x.dst = t₂ := congrArg Move.dst (hxy.trans hty.symm)
      rw [hd2] at hr1
      have h3 : c.fwd = 0 := by omega
      rcases fwd_ne_zero c with h | h <;> rw [h] at h3 <;> exact absurd h3 (by decide)
  · rw [List.nodup_append]
    refine ⟨nodup_flatMap_mk p s c, List.nodup_nil, ?_⟩
    intro x hx y hy hxy
    exact False.elim (List.not_mem_nil hy)

theorem pieceMoves_eq_of_nonpawn (p : Pos) (s : Sq) (q : Piece) (hk : q.kind ≠ .pawn) :
    pieceMoves p s q =
      ((attacks p.board s q).filter fun t => !(p.board t).any (·.color == q.color)).map
        fun t => ⟨s, t, none⟩ := by
  obtain ⟨c, k⟩ := q
  cases k <;> first | rfl | exact absurd rfl hk

theorem pieceMoves_eq_pawn (p : Pos) (s : Sq) (q : Piece) (hk : q.kind = .pawn) :
    pieceMoves p s q = pawnMoves p s q.color := by
  obtain ⟨c, k⟩ := q
  cases k <;> first | rfl | exact Kind.noConfusion hk

theorem pieceMoves_nodup (p : Pos) (s : Sq) (q : Piece) : (pieceMoves p s q).Nodup := by
  by_cases hk : q.kind = .pawn
  · rw [pieceMoves_eq_pawn p s q hk]
    exact pawnMoves_nodup p s q.color
  · rw [pieceMoves_eq_of_nonpawn p s q hk]
    apply nodup_map_of_inj
    · exact List.Nodup.sublist List.filter_sublist (attacks_nodup p.board s q)
    · intro x _ y _ hxy
      simp only [Move.mk.injEq] at hxy
      exact hxy.2.1

theorem castleMoves_eq (p : Pos) :
    castleMoves p =
      if p.board (sq 4 p.turn.home) == some ⟨p.turn, .king⟩ &&
          !attacked p.board (sq 4 p.turn.home) p.turn.opp then
        (if p.castleK p.turn && p.board (sq 7 p.turn.home) == some ⟨p.turn, .rook⟩ &&
            ([5, 6].all fun f => empty p.board (sq f p.turn.home)) &&
            !attacked p.board (sq 5 p.turn.home) p.turn.opp then
          [(⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ : Move)] else []) ++
        (if p.castleQ p.turn && p.board (sq 0 p.turn.home) == some ⟨p.turn, .rook⟩ &&
            ([1, 2, 3].all fun f => empty p.board (sq f p.turn.home)) &&
            !attacked p.board (sq 3 p.turn.home) p.turn.opp then
          [(⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ : Move)] else [])
      else [] := rfl

theorem mem_castleMoves_parts (p : Pos) (m : Move) (hm : m ∈ castleMoves p) :
    m.src = sq 4 p.turn.home ∧
    (m.dst = sq 6 p.turn.home ∨ m.dst = sq 2 p.turn.home) ∧
    p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ := by
  rw [castleMoves_eq] at hm
  split at hm
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    have hkb : p.board (sq 4 p.turn.home) = some ⟨p.turn, .king⟩ :=
      beq_iff_eq.mp hcond.1
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · split at hm
      · rw [List.mem_singleton] at hm
        rw [hm]
        exact ⟨rfl, Or.inl rfl, hkb⟩
      · exact False.elim (List.not_mem_nil hm)
    · split at hm
      · rw [List.mem_singleton] at hm
        rw [hm]
        exact ⟨rfl, Or.inr rfl, hkb⟩
      · exact False.elim (List.not_mem_nil hm)
  · exact False.elim (List.not_mem_nil hm)

theorem nodup_castleMoves (p : Pos) : (castleMoves p).Nodup := by
  rw [castleMoves_eq]
  split
  · rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · split
      · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
      · exact List.nodup_nil
    · split
      · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
      · exact List.nodup_nil
    · intro x hx y hy hxy
      split at hx
      · rw [List.mem_singleton] at hx
        split at hy
        · rw [List.mem_singleton] at hy
          rw [hx, hy] at hxy
          have hr : p.turn.home < 8 := home_lt p.turn
          have hv : (p.turn.home * 8 + 6) % 64 = (p.turn.home * 8 + 2) % 64 :=
            congrArg (fun m => m.dst.val) hxy
          omega
        · exact False.elim (List.not_mem_nil hy)
      · exact False.elim (List.not_mem_nil hx)
  · exact List.nodup_nil

theorem mem_pieceMoves_src (p : Pos) (s : Sq) (q : Piece) (m : Move)
    (hm : m ∈ pieceMoves p s q) : m.src = s := by
  by_cases hk : q.kind = .pawn
  · rw [pieceMoves_eq_pawn p s q hk, pawnMoves_eq] at hm
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · rw [List.mem_flatMap] at hm
      obtain ⟨t, -, hmk⟩ := hm
      exact (mem_mk_part hmk).2
    · rw [List.mem_map] at hm
      obtain ⟨t, -, htm⟩ := hm
      rw [← htm]
  · rw [pieceMoves_eq_of_nonpawn p s q hk] at hm
    rw [List.mem_map] at hm
    obtain ⟨t, -, htm⟩ := hm
    rw [← htm]

theorem queenD_fst (d : Int × Int) (hd : d ∈ queenD) : d.1 = -1 ∨ d.1 = 0 ∨ d.1 = 1 := by
  simp only [queenD, rookD, bishopD, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pseudo_eq (p : Pos) : pseudo p =
    allSq.flatMap (fun s => match p.board s with
      | some q => if q.color == p.turn then pieceMoves p s q else []
      | none => []) ++ castleMoves p := rfl

theorem mem_pseudo_gen (p : Pos) (s : Sq) (m : Move)
    (hm : m ∈ (match p.board s with
      | some q => if q.color == p.turn then pieceMoves p s q else []
      | none => [])) : m.src = s := by
  split at hm
  · split at hm
    · exact mem_pieceMoves_src p s _ m hm
    · exact False.elim (List.not_mem_nil hm)
  · exact False.elim (List.not_mem_nil hm)

theorem pseudo_nodup (p : Pos) : (pseudo p).Nodup := by
  rw [pseudo_eq, List.nodup_append]
  refine ⟨?_, nodup_castleMoves p, ?_⟩
  · apply nodup_flatMap (List.nodup_finRange 64)
    · intro s _
      split
      · split
        · exact pieceMoves_nodup p s _
        · exact List.nodup_nil
      · exact List.nodup_nil
    · intro s₁ _ s₂ _ h12 x hx y hy hxy
      have h1 := congrArg Move.src hxy
      rw [mem_pseudo_gen p s₁ x hx, mem_pseudo_gen p s₂ y hy] at h1
      exact h12 h1
  · intro x hx y hy hxy
    rw [List.mem_flatMap] at hx
    obtain ⟨s, -, hx⟩ := hx
    obtain ⟨hys, hyd, hyk⟩ := mem_castleMoves_parts p y hy
    have hxs : x.src = s := mem_pseudo_gen p s x hx
    have hsr : s = sq 4 p.turn.home := by
      have h1 := congrArg Move.src hxy
      rw [hxs, hys] at h1
      exact h1
    split at hx
    · rename_i heq
      split at hx
      · have h1 : p.board (sq 4 p.turn.home) = some _ := hsr ▸ heq
        rw [hyk] at h1
        have hq := (Option.some.inj h1).symm
        subst hq
        rw [pieceMoves_eq_of_nonpawn p s ⟨p.turn, .king⟩ (fun h => Kind.noConfusion h)] at hx
        rw [List.mem_map] at hx
        obtain ⟨t, htf, htx⟩ := hx
        have hdst : x.dst = t := (congrArg Move.dst htx).symm
        have hdeq : t = y.dst := hdst ▸ congrArg Move.dst hxy
        have hta : t ∈ steps s queenD := (List.mem_filter.mp htf).1
        simp only [steps, List.mem_filterMap] at hta
        obtain ⟨d, hd, hoff⟩ := hta
        obtain ⟨fd, -⟩ := off_some_sub s t d.1 d.2 hoff
        have hqb := queenD_fst d hd
        have hs4 : (s.file : Int) = 4 := by
          rw [hsr]
          have := file_sq 4 p.turn.home (by decide) (home_lt p.turn)
          omega
        have htf6 : (t.file : Int) = 6 ∨ (t.file : Int) = 2 := by
          rcases hyd with hyd | hyd
          · rw [hdeq, hyd]
            have := file_sq 6 p.turn.home (by decide) (home_lt p.turn)
            omega
          · rw [hdeq, hyd]
            have := file_sq 2 p.turn.home (by decide) (home_lt p.turn)
            omega
        rcases htf6 with h6 | h6 <;> rcases hqb with hd1 | hd1 | hd1 <;> omega
      · exact False.elim (List.not_mem_nil hx)
    · exact False.elim (List.not_mem_nil hx)

theorem legalMoves_nodup (p : Pos) : (legalMoves p).Nodup :=
  List.Nodup.sublist List.filter_sublist (pseudo_nodup p)

theorem flipMove_flipMove (m : Move) : flipMove (flipMove m) = m := by
  obtain ⟨a, b, k⟩ := m
  show (⟨flipSq (flipSq a), flipSq (flipSq b), k⟩ : Move) = ⟨a, b, k⟩
  rw [flipSq_flipSq, flipSq_flipSq]

theorem flipMove_injective : Function.Injective flipMove := by
  intro a b h
  have h2 := congrArg flipMove h
  rwa [flipMove_flipMove, flipMove_flipMove] at h2

theorem filter_flip_length (P : Sq → Bool) :
    (allSq.filter fun s => P (flipSq s)).length = (allSq.filter P).length := by
  apply Nat.le_antisymm
  · have hnd : ((allSq.filter fun s => P (flipSq s)).map flipSq).Nodup := by
      apply nodup_map_of_inj
      · exact List.Nodup.sublist List.filter_sublist (List.nodup_finRange 64)
      · exact fun x _ y _ h => flipSq_injective h
    have hsub : (allSq.filter fun s => P (flipSq s)).map flipSq ⊆ allSq.filter P := by
      intro m hm
      rw [List.mem_map] at hm
      obtain ⟨s, hs, rfl⟩ := hm
      rw [List.mem_filter] at hs ⊢
      exact ⟨List.mem_finRange _, hs.2⟩
    have hl := List.Nodup.length_le_of_subset hnd hsub
    rwa [List.length_map] at hl
  · have hnd : ((allSq.filter P).map flipSq).Nodup := by
      apply nodup_map_of_inj
      · exact List.Nodup.sublist List.filter_sublist (List.nodup_finRange 64)
      · exact fun x _ y _ h => flipSq_injective h
    have hsub : (allSq.filter P).map flipSq ⊆ allSq.filter (fun s => P (flipSq s)) := by
      intro m hm
      rw [List.mem_map] at hm
      obtain ⟨s, hs, rfl⟩ := hm
      rw [List.mem_filter] at hs ⊢
      refine ⟨List.mem_finRange _, ?_⟩
      rw [flipSq_flipSq]
      exact hs.2
    have hl := List.Nodup.length_le_of_subset hnd hsub
    rwa [List.length_map] at hl

theorem map_flipPiece_beq (o : Option Piece) (c : Color) (k : Kind) :
    (o.map flipPiece == some ⟨c, k⟩) = (o == some ⟨c.opp, k⟩) := by
  cases o with
  | none => rfl
  | some q =>
    obtain ⟨c₂, k₂⟩ := q
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    constructor
    · intro h
      have h' : some (flipPiece ⟨c₂, k₂⟩) = some ⟨c, k⟩ := h
      have h3 := Option.some.inj h'
      simp only [flipPiece, Piece.mk.injEq, Option.some.injEq] at h3 ⊢
      obtain ⟨hc2, hk2⟩ := h3
      constructor
      · have e := congrArg Color.opp hc2
        rw [opp_opp] at e
        exact e
      · exact hk2
    · intro h
      simp only [Option.some.injEq, Piece.mk.injEq] at h
      obtain ⟨hc2, hk2⟩ := h
      have h' : some (flipPiece ⟨c₂, k₂⟩) = some ⟨c, k⟩ := by
        simp only [flipPiece, Option.some.injEq, Piece.mk.injEq]
        exact ⟨by rw [hc2, opp_opp], hk2⟩
      exact h'

theorem countSq_flip (b : Board) (P : Option Piece → Bool) :
    countSq (flipBoard b) P = countSq b fun o => P (o.map flipPiece) := by
  show (allSq.filter fun s => P ((b (flipSq s)).map flipPiece)).length =
    (allSq.filter fun s => P ((b s).map flipPiece)).length
  exact filter_flip_length (fun s => P ((b s).map flipPiece))

theorem cnt_flip (b : Board) (c : Color) (k : Kind) :
    cnt (flipBoard b) c k = cnt b c.opp k := by
  show (allSq.filter fun s => (flipBoard b s == some ⟨c, k⟩)).length =
    (allSq.filter fun s => (b s == some ⟨c.opp, k⟩)).length
  have hpoint : ∀ s : Sq, (flipBoard b s == some ⟨c, k⟩) = (b (flipSq s) == some ⟨c.opp, k⟩) := by
    intro s
    show ((b (flipSq s)).map flipPiece == some ⟨c, k⟩) = (b (flipSq s) == some ⟨c.opp, k⟩)
    exact map_flipPiece_beq _ c k
  have hrw := List.filter_congr (l := allSq) (fun s _ => hpoint s)
  rw [hrw]
  exact filter_flip_length (fun s => (b s == some ⟨c.opp, k⟩))

theorem parity_flip (s : Sq) : parity (flipSq s) = (parity s + 1) % 2 := by
  have hr : s.rank < 8 := by
    have := s.isLt
    show s.val / 8 < 8
    omega
  unfold parity
  rw [flipSq_file, flipSq_rank]
  omega

theorem cntB_flip (b : Board) (c : Color) (par : Nat) (hp : par < 2) :
    cntB (flipBoard b) c par = cntB b c.opp ((par + 1) % 2) := by
  show (allSq.filter fun s => ((flipBoard b s == some ⟨c, .bishop⟩) && (parity s == par))).length =
    (allSq.filter fun s => ((b s == some ⟨c.opp, .bishop⟩) && (parity s == (par + 1) % 2))).length
  have hpoint : ∀ s : Sq,
      ((flipBoard b s == some ⟨c, .bishop⟩) && (parity s == par)) =
        ((b (flipSq s) == some ⟨c.opp, .bishop⟩) && (parity (flipSq s) == (par + 1) % 2)) := by
    intro s
    show (((b (flipSq s)).map flipPiece == some ⟨c, .bishop⟩) && (parity s == par)) = _
    rw [map_flipPiece_beq, parity_flip]
    generalize hps : parity s = ps
    have hps2 : ps < 2 := by
      rw [← hps]
      exact Nat.mod_lt _ (by decide)
    have hor : ps = 0 ∨ ps = 1 := by omega
    have hpar : par = 0 ∨ par = 1 := by omega
    rcases hor with rfl | rfl <;> rcases hpar with rfl | rfl <;> rfl
  have hrw := List.filter_congr (l := allSq) (fun s _ => hpoint s)
  rw [hrw]
  exact filter_flip_length (fun s => ((b s == some ⟨c.opp, .bishop⟩) && (parity s == (par + 1) % 2)))

theorem any_map_flip (o : Option Piece) (c : Color) :
    ((o.map flipPiece).any fun q => q.color == c) = (o.any fun q => q.color == c.opp) := by
  cases o with
  | none => rfl
  | some q =>
    obtain ⟨c₂, k₂⟩ := q
    cases c₂ <;> cases c <;> rfl

theorem men_flip (b : Board) (c : Color) : men (flipBoard b) c = men b c.opp := by
  show (allSq.filter fun s => ((flipBoard b s).any fun q => q.color == c)).length =
    (allSq.filter fun s => ((b s).any fun q => q.color == c.opp)).length
  have hpoint : ∀ s : Sq, ((flipBoard b s).any fun q => q.color == c) =
      ((b (flipSq s)).any fun q => q.color == c.opp) := by
    intro s
    show (((b (flipSq s)).map flipPiece).any fun q => q.color == c) = _
    exact any_map_flip _ c
  have hrw := List.filter_congr (l := allSq) (fun s _ => hpoint s)
  rw [hrw]
  exact filter_flip_length (fun s => ((b s).any fun q => q.color == c.opp))

theorem file_lt (u : Sq) : u.file < 8 := Nat.mod_lt _ (by decide)

theorem flipSq_sq (f r : Nat) (hf : f < 8) (hr : r < 8) : flipSq (sq f r) = sq f (7 - r) := by
  apply Fin.ext
  show ((r * 8 + f) % 64) ^^^ 56 = ((7 - r) * 8 + f) % 64
  have h1 : r * 8 + f < 64 := by omega
  have h2 : (7 - r) * 8 + f < 64 := by omega
  have hx : ∀ v, v < 64 → v ^^^ 56 = (7 - v / 8) * 8 + v % 8 := by decide
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, hx _ h1]
  have h3 : (r * 8 + f) / 8 = r := by omega
  have h4 : (r * 8 + f) % 8 = f := by omega
  rw [h3, h4]

theorem natAbs_sub_comm' (x y : Int) : (x - y).natAbs = (y - x).natAbs := by
  rw [show x - y = -(y - x) from by omega, Int.natAbs_neg]

theorem dist_flip (a b : Sq) : dist (flipSq a) (flipSq b) = dist a b := by
  unfold dist
  rw [flipSq_file, flipSq_file, flipSq_rank, flipSq_rank]
  have hra : a.rank ≤ 7 := by
    have := a.isLt
    show a.val / 8 ≤ 7
    omega
  have hrb : b.rank ≤ 7 := by
    have := b.isLt
    show b.val / 8 ≤ 7
    omega
  have e : ((7 - a.rank : Nat) : Int) - ((7 - b.rank : Nat) : Int) =
      -(((a.rank : Int) - b.rank)) := by omega
  rw [e, Int.natAbs_neg]

theorem dist_comm (a b : Sq) : dist a b = dist b a := by
  unfold dist
  rw [natAbs_sub_comm' (a.file : Int) (b.file : Int),
    natAbs_sub_comm' (a.rank : Int) (b.rank : Int)]

theorem kingSq_flip (p : Pos) (c : Color) (hk : ∀ c, cnt p.board c .king = 1) :
    kingSq (flipPos p) c = flipSq (kingSq p c.opp) := by
  have hk1 : cnt (flipPos p).board c .king = 1 := by
    show cnt (flipBoard p.board) c .king = 1
    rw [cnt_flip]
    exact hk c.opp
  obtain ⟨-, huniq⟩ := kingSq_spec (flipPos p) c hk1
  have hbval : p.board (kingSq p c.opp) = some ⟨c.opp, .king⟩ :=
    (kingSq_spec p c.opp (hk c.opp)).1
  have hbv : (flipPos p).board (flipSq (kingSq p c.opp)) = some ⟨c, .king⟩ := by
    show (p.board (flipSq (flipSq (kingSq p c.opp)))).map flipPiece = some ⟨c, .king⟩
    rw [flipSq_flipSq, hbval]
    cases c <;> rfl
  exact (huniq _ hbv).symm

theorem epOk_flip (p : Pos) (u : Sq) (hepu : EpOk p u) : EpOk (flipPos p) (flipSq u) := by
  obtain ⟨b, t, ck, cq, e⟩ := p
  cases t with
  | white =>
    have hw : u.rank = 5 ∧ b (sq u.file 4) = some ⟨.black, .pawn⟩ ∧ b u = none ∧
        b (sq u.file 6) = none := hepu
    obtain ⟨h1, h2, h3, h4⟩ := hw
    show (flipSq u).rank = 2 ∧
      (flipPos ⟨b, .white, ck, cq, e⟩).board (sq (flipSq u).file 3) = some ⟨.white, .pawn⟩ ∧
      (flipPos ⟨b, .white, ck, cq, e⟩).board (flipSq u) = none ∧
      (flipPos ⟨b, .white, ck, cq, e⟩).board (sq (flipSq u).file 1) = none
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [flipSq_rank, h1]
    · show (b (flipSq (sq (flipSq u).file 3))).map flipPiece = some ⟨.white, .pawn⟩
      rw [flipSq_file, flipSq_sq u.file 3 (file_lt u) (by decide)]
      show (b (sq u.file 4)).map flipPiece = some ⟨.white, .pawn⟩
      rw [h2]
      rfl
    · show (b (flipSq (flipSq u))).map flipPiece = none
      rw [flipSq_flipSq, h3]
      rfl
    · show (b (flipSq (sq (flipSq u).file 1))).map flipPiece = none
      rw [flipSq_file, flipSq_sq u.file 1 (file_lt u) (by decide)]
      show (b (sq u.file 6)).map flipPiece = none
      rw [h4]
      rfl
  | black =>
    have hw : u.rank = 2 ∧ b (sq u.file 3) = some ⟨.white, .pawn⟩ ∧ b u = none ∧
        b (sq u.file 1) = none := hepu
    obtain ⟨h1, h2, h3, h4⟩ := hw
    show (flipSq u).rank = 5 ∧
      (flipPos ⟨b, .black, ck, cq, e⟩).board (sq (flipSq u).file 4) = some ⟨.black, .pawn⟩ ∧
      (flipPos ⟨b, .black, ck, cq, e⟩).board (flipSq u) = none ∧
      (flipPos ⟨b, .black, ck, cq, e⟩).board (sq (flipSq u).file 6) = none
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [flipSq_rank, h1]
    · show (b (flipSq (sq (flipSq u).file 4))).map flipPiece = some ⟨.black, .pawn⟩
      rw [flipSq_file, flipSq_sq u.file 4 (file_lt u) (by decide)]
      show (b (sq u.file 3)).map flipPiece = some ⟨.black, .pawn⟩
      rw [h2]
      rfl
    · show (b (flipSq (flipSq u))).map flipPiece = none
      rw [flipSq_flipSq, h3]
      rfl
    · show (b (flipSq (sq (flipSq u).file 6))).map flipPiece = none
      rw [flipSq_file, flipSq_sq u.file 6 (file_lt u) (by decide)]
      show (b (sq u.file 1)).map flipPiece = none
      rw [h4]
      rfl

theorem admissible_flip (p : Pos) (h : Admissible p) : Admissible (flipPos p) := by
  obtain ⟨kings, apart, noBackPawn, safe, menLe, material, castleK, castleQ, ep⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    show cnt (flipBoard p.board) c .king = 1
    rw [cnt_flip]
    exact kings c.opp
  · rw [kingSq_flip p .white kings, kingSq_flip p .black kings, dist_flip]
    show 1 < dist (kingSq p .black) (kingSq p .white)
    rw [dist_comm]
    exact apart
  · intro s c hr hb2
    have h1 : (p.board (flipSq s)).map flipPiece = some ⟨c, .pawn⟩ := hb2
    rw [Option.map_eq_some_iff] at h1
    obtain ⟨⟨ca, ka⟩, ha, ha2⟩ := h1
    simp only [flipPiece, Piece.mk.injEq] at ha2
    have hca : ca = c.opp := by
      have e2 := congrArg Color.opp ha2.1
      rw [opp_opp] at e2
      exact e2
    have hka : ka = .pawn := ha2.2
    exact noBackPawn (flipSq s) c.opp
      (by rw [flipSq_rank]; rcases hr with hr | hr <;> omega)
      (by rw [ha, hca, hka])
  · show inCheck (flipPos p) p.turn.opp.opp = false
    rw [inCheck_flip]
    exact safe
  · intro c
    show men (flipBoard p.board) c ≤ 16
    rw [men_flip]
    exact menLe c.opp
  · intro c
    show excess (flipBoard p.board) c ≤ 8
    unfold excess
    have h1 : ∀ k, cnt (flipBoard p.board) c k = cnt p.board c.opp k := fun k => cnt_flip ..
    have h2 : cntB (flipBoard p.board) c 0 = cntB p.board c.opp 1 :=
      cntB_flip p.board c 0 (by decide)
    have h3 : cntB (flipBoard p.board) c 1 = cntB p.board c.opp 0 :=
      cntB_flip p.board c 1 (by decide)
    simp only [h1, h2, h3]
    have hm := material c.opp
    unfold excess at hm
    omega
  · intro c hkc
    have hk2 : p.castleK c.opp = true := hkc
    obtain ⟨h4, h7⟩ := castleK c.opp hk2
    have e4 : flipSq (sq 4 c.home) = sq 4 c.opp.home := by
      rw [flipSq_sq 4 c.home (by decide) (home_lt c)]
      congr 1
      cases c <;> rfl
    have e7 : flipSq (sq 7 c.home) = sq 7 c.opp.home := by
      rw [flipSq_sq 7 c.home (by decide) (home_lt c)]
      congr 1
      cases c <;> rfl
    constructor
    · show (p.board (flipSq (sq 4 c.home))).map flipPiece = some ⟨c, .king⟩
      rw [e4, h4]
      cases c <;> rfl
    · show (p.board (flipSq (sq 7 c.home))).map flipPiece = some ⟨c, .rook⟩
      rw [e7, h7]
      cases c <;> rfl
  · intro c hqc
    have hq2 : p.castleQ c.opp = true := hqc
    obtain ⟨h4, h0⟩ := castleQ c.opp hq2
    have e4 : flipSq (sq 4 c.home) = sq 4 c.opp.home := by
      rw [flipSq_sq 4 c.home (by decide) (home_lt c)]
      congr 1
      cases c <;> rfl
    have e0 : flipSq (sq 0 c.home) = sq 0 c.opp.home := by
      rw [flipSq_sq 0 c.home (by decide) (home_lt c)]
      congr 1
      cases c <;> rfl
    constructor
    · show (p.board (flipSq (sq 4 c.home))).map flipPiece = some ⟨c, .king⟩
      rw [e4, h4]
      cases c <;> rfl
    · show (p.board (flipSq (sq 0 c.home))).map flipPiece = some ⟨c, .rook⟩
      rw [e0, h0]
      cases c <;> rfl
  · intro t het
    have hep : p.ep.map flipSq = some t := het
    cases hep2 : p.ep with
    | none =>
      rw [hep2, Option.map_none] at hep
      cases hep
    | some u =>
      rw [hep2] at hep
      have hep' : some (flipSq u) = some t := hep
      have hut : flipSq u = t := Option.some.inj hep'
      have hepu := ep u hep2
      subst hut
      exact epOk_flip p u hepu

theorem fwd_flip (c : Color) : c.opp.fwd = -c.fwd := by cases c <;> rfl

theorem home_flip (c : Color) : c.opp.home = 7 - c.home := by cases c <;> rfl

theorem pawnHome_flip (c : Color) : c.opp.pawnHome = 7 - c.pawnHome := by cases c <;> rfl

theorem last_flip (c : Color) : c.opp.last = 7 - c.last := by cases c <;> rfl

theorem c3_rank_lt (s : Sq) : s.rank < 8 := by
  have := s.isLt
  show s.val / 8 < 8
  omega

theorem c3_beq_rank7 (a b : Nat) (ha : a < 8) (hb : b < 8) : ((7 - a == 7 - b) = (a == b)) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor <;> intro h <;> omega

theorem c3_mem_flipMove (m : Move) (l : List Move) : flipMove m ∈ l.map flipMove ↔ m ∈ l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, hx2⟩
    have h3 := flipMove_injective hx2
    rwa [h3] at hx
  · intro h
    exact ⟨m, h, rfl⟩

theorem c3_flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem two_fwd_flip (c : Color) : 2 * c.opp.fwd = -(2 * c.fwd) := by cases c <;> rfl

theorem c3_off_fwd (s : Sq) (c : Color) :
    off (flipSq s) 0 c.opp.fwd = (off s 0 c.fwd).map flipSq := by
  have h := off_flip s 0 c.fwd
  rwa [← fwd_flip] at h

theorem c3_off_two (s : Sq) (c : Color) :
    off (flipSq s) 0 (2 * c.opp.fwd) = (off s 0 (2 * c.fwd)).map flipSq := by
  have h := off_flip s 0 (2 * c.fwd)
  rwa [← two_fwd_flip] at h

theorem c3_filter_map_opt (o : Option Sq) (P : Sq → Bool) :
    ((o.map flipSq).filter P) = (o.filter fun t => P (flipSq t)).map flipSq := by
  cases o with
  | none => rfl
  | some t =>
    show (if P (flipSq t) then some (flipSq t) else none) =
      (if P (flipSq t) then some t else (none : Option Sq)).map flipSq
    by_cases h : P (flipSq t)
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      rfl

theorem c3_filter_opt_congr (o : Option Sq) {P Q : Sq → Bool} (h : ∀ t, P t = Q t) :
    o.filter P = o.filter Q := by
  cases o with
  | none => rfl
  | some t =>
    show (if P t then some t else none) = if Q t then some t else none
    rw [h t]

theorem foe_flip (b : Board) (c : Color) (t : Sq) :
    foe (flipBoard b) c.opp (flipSq t) = foe b c t := by
  show (match (b (flipSq (flipSq t))).map flipPiece with
      | some q => q.color != c.opp | none => false) =
    (match b t with | some q => q.color != c | none => false)
  rw [flipSq_flipSq]
  generalize b t = o
  cases o with
  | none => rfl
  | some q =>
    show ((flipPiece q).color != c.opp) = (q.color != c)
    obtain ⟨cq, kq⟩ := q
    cases cq <;> cases c <;> rfl

theorem c3_beq_map_flipSq (o : Option Sq) (t : Sq) :
    (o.map flipSq == some (flipSq t)) = (o == some t) := by
  cases o with
  | none => rfl
  | some u =>
    rw [Option.map_some, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    constructor
    · intro h
      exact congrArg some (flipSq_injective (Option.some.inj h))
    · intro h
      exact congrArg (Option.map flipSq) h

theorem epCap_flip (p : Pos) (c : Color) (t : Sq) :
    epCap (flipPos p) c.opp (flipSq t) = epCap p c t := by
  have hoff : off (flipSq t) 0 (c.fwd) = (off t 0 (-c.fwd)).map flipSq := by
    have h := off_flip t 0 (-c.fwd)
    rwa [Int.neg_neg] at h
  show (((p.ep.map flipSq) == some (flipSq t)) && empty (flipBoard p.board) (flipSq t) &&
      (match off (flipSq t) 0 (-c.opp.fwd) with
        | some u => (flipBoard p.board) u == some ⟨c.opp.opp, .pawn⟩
        | none => false)) =
    ((p.ep == some t) && empty p.board t &&
      (match off t 0 (-c.fwd) with
        | some u => p.board u == some ⟨c.opp, .pawn⟩
        | none => false))
  rw [c3_beq_map_flipSq, empty_flip, fwd_flip, Int.neg_neg, hoff]
  have hpt : ∀ o : Option Sq,
      (match o.map flipSq with
        | some u => ((flipBoard p.board) u == some (⟨c.opp.opp, .pawn⟩ : Piece))
        | none => false) =
      (match o with
        | some u => (p.board u == some (⟨c.opp, .pawn⟩ : Piece))
        | none => false) := by
    intro o
    cases o with
    | none => rfl
    | some u =>
      show ((flipBoard p.board) (flipSq u) == some (⟨c.opp.opp, .pawn⟩ : Piece)) =
        (p.board u == some (⟨c.opp, .pawn⟩ : Piece))
      rw [opp_opp]
      show ((p.board (flipSq (flipSq u))).map flipPiece == some (⟨c, .pawn⟩ : Piece)) =
        (p.board u == some (⟨c.opp, .pawn⟩ : Piece))
      rw [flipSq_flipSq]
      exact map_flipPiece_beq _ _ _
  rw [hpt]

theorem c3_steps_pawn_flip (s : Sq) (c : Color) :
    steps (flipSq s) [(1, c.opp.fwd), (-1, c.opp.fwd)] =
      (steps s [(1, c.fwd), (-1, c.fwd)]).map flipSq := by
  have h1 : steps (flipSq s) [(1, c.opp.fwd), (-1, c.opp.fwd)] =
      List.filterMap (fun d => off (flipSq s) d.1 d.2) [(1, c.opp.fwd), (-1, c.opp.fwd)] := rfl
  rw [h1]
  have h2 : ∀ (ds : List (Int × Int)),
      List.filterMap (fun d => off (flipSq s) d.1 d.2) ds =
      (List.filterMap (fun d => off s d.1 (-d.2)) ds).map flipSq := by
    intro ds
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      rw [List.filterMap_cons, List.filterMap_cons]
      have hoff : off (flipSq s) d.1 d.2 = (off s d.1 (-d.2)).map flipSq := by
        have h := off_flip s d.1 (-d.2)
        rwa [Int.neg_neg] at h
      rw [hoff]
      cases off s d.1 (-d.2) with
      | none => exact ih
      | some t =>
        show flipSq t :: List.filterMap (fun d => off (flipSq s) d.1 d.2) ds =
          (t :: List.filterMap (fun d => off s d.1 (-d.2)) ds).map flipSq
        rw [List.map_cons, ih]
  rw [h2]
  cases c <;> rfl

theorem c3_one_flip (p : Pos) (s : Sq) (c : Color) :
    ((off (flipSq s) 0 c.opp.fwd).filter (empty (flipPos p).board)) =
      ((off s 0 c.fwd).filter (empty p.board)).map flipSq := by
  rw [c3_off_fwd, c3_filter_map_opt]
  apply congrArg (Option.map flipSq)
  apply c3_filter_opt_congr
  intro t
  show empty (flipBoard p.board) (flipSq t) = empty p.board t
  exact empty_flip _ _

theorem c3_caps_flip (p : Pos) (s : Sq) (c : Color) :
    ((steps (flipSq s) [(1, c.opp.fwd), (-1, c.opp.fwd)]).filter fun t =>
        foe (flipPos p).board c.opp t || epCap (flipPos p) c.opp t) =
      ((steps s [(1, c.fwd), (-1, c.fwd)]).filter fun t =>
        foe p.board c t || epCap p c t).map flipSq := by
  rw [c3_steps_pawn_flip, List.filter_map]
  apply congrArg (List.map flipSq)
  apply List.filter_congr
  intro t _
  show (foe (flipBoard p.board) c.opp (flipSq t) || epCap (flipPos p) c.opp (flipSq t)) =
    (foe p.board c t || epCap p c t)
  rw [foe_flip, epCap_flip]

theorem c3_mk_flip (s t : Sq) (c : Color) :
    (if (flipSq t).rank == c.opp.last then [Kind.knight, .bishop, .rook, .queen].map fun k =>
        (⟨flipSq s, flipSq t, some k⟩ : Move)
      else [(⟨flipSq s, flipSq t, none⟩ : Move)]) =
      (if t.rank == c.last then [Kind.knight, .bishop, .rook, .queen].map fun k =>
        (⟨s, t, some k⟩ : Move)
      else [(⟨s, t, none⟩ : Move)]).map flipMove := by
  have hcond : ((flipSq t).rank == c.opp.last) = (t.rank == c.last) := by
    rw [flipSq_rank, last_flip]
    exact c3_beq_rank7 _ _ (c3_rank_lt t) (by cases c <;> decide)
  by_cases h : t.rank == c.last
  · rw [hcond, if_pos h, if_pos h, List.map_map]
    rfl
  · rw [hcond, if_neg h, if_neg h]
    rfl

theorem c3_two_flip (p : Pos) (s : Sq) (c : Color) :
    (if (flipSq s).rank == c.opp.pawnHome &&
        ((off (flipSq s) 0 c.opp.fwd).filter (empty (flipPos p).board)).isSome then
      (off (flipSq s) 0 (2 * c.opp.fwd)).filter (empty (flipPos p).board) else none) =
      (if s.rank == c.pawnHome && ((off s 0 c.fwd).filter (empty p.board)).isSome then
        (off s 0 (2 * c.fwd)).filter (empty p.board) else none).map flipSq := by
  have hcond : ((flipSq s).rank == c.opp.pawnHome) = (s.rank == c.pawnHome) := by
    rw [flipSq_rank, pawnHome_flip]
    exact c3_beq_rank7 _ _ (c3_rank_lt s) (by cases c <;> decide)
  have his : (((off (flipSq s) 0 c.opp.fwd).filter (empty (flipPos p).board)).isSome) =
      (((off s 0 c.fwd).filter (empty p.board)).isSome) := by
    rw [c3_one_flip, Option.isSome_map]
  have hoff : (off (flipSq s) 0 (2 * c.opp.fwd)).filter (empty (flipPos p).board) =
      ((off s 0 (2 * c.fwd)).filter (empty p.board)).map flipSq := by
    rw [c3_off_two, c3_filter_map_opt]
    exact congrArg (Option.map flipSq) (c3_filter_opt_congr _ fun t => empty_flip _ _)
  rw [hcond, his, hoff]
  rw [apply_ite (Option.map flipSq)]
  rfl

theorem c3_map_congr_simple {α β : Type} {l : List α} {f g : α → β}
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem c3_pawnMoves_flip (p : Pos) (s : Sq) (c : Color) :
    pawnMoves (flipPos p) (flipSq s) c.opp = (pawnMoves p s c).map flipMove := by
  rw [pawnMoves_eq (flipPos p) (flipSq s) c.opp, pawnMoves_eq p s c]
  rw [c3_two_flip, c3_one_flip, c3_caps_flip]
  rw [Option.toList_map, Option.toList_map]
  rw [← List.map_append, List.flatMap_map, List.map_map]
  rw [List.map_append, List.map_flatMap, List.map_map]
  congr 1
  apply c3_flatMap_congr
  intro t _
  exact c3_mk_flip s t c

theorem mem_pawnMoves_flip (p : Pos) (s : Sq) (c : Color) (m : Move) :
    flipMove m ∈ pawnMoves (flipPos p) (flipSq s) c.opp ↔ m ∈ pawnMoves p s c := by
  rw [c3_pawnMoves_flip]
  exact c3_mem_flipMove m _

theorem c3_own_filter_flip (p : Pos) (q : Piece) (t : Sq) :
    (!((flipPos p).board (flipSq t)).any (·.color == (flipPiece q).color)) =
    (!(p.board t).any (·.color == q.color)) := by
  obtain ⟨cq, kq⟩ := q
  show (!((p.board (flipSq (flipSq t))).map flipPiece).any (·.color ==
      (flipPiece ⟨cq, kq⟩).color)) = (!(p.board t).any (·.color == cq))
  rw [flipSq_flipSq]
  cases p.board t with
  | none => rfl
  | some x =>
    obtain ⟨cx, kx⟩ := x
    cases cx <;> cases cq <;> rfl

theorem c3_mem_pieceMoves_flip_np (p : Pos) (s : Sq) (q : Piece) (m : Move)
    (hk : q.kind ≠ .pawn) :
    flipMove m ∈ pieceMoves (flipPos p) (flipSq s) (flipPiece q) ↔ m ∈ pieceMoves p s q := by
  have hk' : (flipPiece q).kind ≠ .pawn := fun h => hk h
  rw [pieceMoves_eq_of_nonpawn (flipPos p) (flipSq s) (flipPiece q) hk',
    pieceMoves_eq_of_nonpawn p s q hk, List.mem_map, List.mem_map]
  constructor
  · rintro ⟨t, ht, htm⟩
    refine ⟨m.dst, ?_, ?_⟩
    · rw [List.mem_filter] at ht
      obtain ⟨hatt, hown⟩ := ht
      have hdst : t = flipSq m.dst := congrArg Move.dst htm
      rw [hdst] at hatt hown
      rw [List.mem_filter]
      exact ⟨(mem_attacks_flip p.board s m.dst q).mp hatt,
        by rwa [c3_own_filter_flip] at hown⟩
    · have hsrc : s = m.src := flipSq_injective (congrArg Move.src htm)
      have hpromo : (none : Option Kind) = m.promo := congrArg Move.promo htm
      rw [hsrc, hpromo]
  · rintro ⟨t, ht, htm⟩
    subst htm
    refine ⟨flipSq t, ?_, rfl⟩
    rw [List.mem_filter] at ht
    obtain ⟨hatt, hown⟩ := ht
    rw [List.mem_filter]
    exact ⟨(mem_attacks_flip p.board s t q).mpr hatt, by rwa [c3_own_filter_flip]⟩

theorem mem_pieceMoves_flip (p : Pos) (s : Sq) (q : Piece) (m : Move) :
    flipMove m ∈ pieceMoves (flipPos p) (flipSq s) (flipPiece q) ↔ m ∈ pieceMoves p s q := by
  by_cases hk : q.kind = .pawn
  · have hk' : (flipPiece q).kind = .pawn := hk
    rw [pieceMoves_eq_pawn (flipPos p) (flipSq s) (flipPiece q) hk',
      pieceMoves_eq_pawn p s q hk]
    show flipMove m ∈ pawnMoves (flipPos p) (flipSq s) (flipPiece q).color ↔
      m ∈ pawnMoves p s q.color
    rw [show (flipPiece q).color = q.color.opp from rfl]
    exact mem_pawnMoves_flip p s q.color m
  · exact c3_mem_pieceMoves_flip_np p s q m hk

theorem c3_flip_sq_home (f : Nat) (hf : f < 8) (c : Color) :
    flipSq (sq f c.opp.home) = sq f c.home := by
  rw [flipSq_sq f c.opp.home hf (home_lt _)]
  congr 1
  cases c <;> rfl

theorem c3_flip_sq_home' (f : Nat) (hf : f < 8) (c : Color) :
    flipSq (sq f c.home) = sq f c.opp.home := by
  rw [flipSq_sq f c.home hf (home_lt _)]
  congr 1
  exact (home_flip c).symm

theorem c3_kingHome_flip (p : Pos) (c : Color) :
    (flipBoard p.board (sq 4 c.opp.home) == some (⟨c.opp, .king⟩ : Piece)) =
    (p.board (sq 4 c.home) == some (⟨c, .king⟩ : Piece)) := by
  show ((p.board (flipSq (sq 4 c.opp.home))).map flipPiece == some (⟨c.opp, .king⟩ : Piece)) = _
  rw [c3_flip_sq_home 4 (by decide) c, map_flipPiece_beq, opp_opp]

theorem c3_rookHome_flip (p : Pos) (c : Color) (f : Nat) (hf : f < 8) :
    (flipBoard p.board (sq f c.opp.home) == some (⟨c.opp, .rook⟩ : Piece)) =
    (p.board (sq f c.home) == some (⟨c, .rook⟩ : Piece)) := by
  show ((p.board (flipSq (sq f c.opp.home))).map flipPiece == some (⟨c.opp, .rook⟩ : Piece)) = _
  rw [c3_flip_sq_home f hf c, map_flipPiece_beq, opp_opp]

theorem c3_attacked_home_flip (p : Pos) (c : Color) (f : Nat) (hf : f < 8) :
    attacked (flipBoard p.board) (sq f c.opp.home) c.opp.opp =
    attacked p.board (sq f c.home) c.opp := by
  rw [← c3_flip_sq_home' f hf c, attacked_flip]

theorem c3_castleK_flip (p : Pos) (c : Color) :
    (flipPos p).castleK c.opp = p.castleK c := by
  show p.castleK c.opp.opp = _
  rw [opp_opp]

theorem c3_castleQ_flip (p : Pos) (c : Color) :
    (flipPos p).castleQ c.opp = p.castleQ c := by
  show p.castleQ c.opp.opp = _
  rw [opp_opp]

theorem c3_all_empty_flip (p : Pos) (fs : List Nat) (c : Color) (hfs : ∀ f ∈ fs, f < 8) :
    (fs.all fun f => empty (flipBoard p.board) (sq f c.opp.home)) =
    (fs.all fun f => empty p.board (sq f c.home)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [List.all_cons, List.all_cons, ih fun g hg => hfs g (List.mem_cons_of_mem _ hg)]
    congr 1
    rw [← c3_flip_sq_home' f (hfs f (List.mem_cons_self ..)) c]
    exact empty_flip p.board (sq f c.home)

theorem c3_mvK (p : Pos) :
    (⟨sq 4 p.turn.opp.home, sq 6 p.turn.opp.home, none⟩ : Move) =
    flipMove ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ := by
  show (⟨sq 4 p.turn.opp.home, sq 6 p.turn.opp.home, none⟩ : Move) =
    ⟨flipSq (sq 4 p.turn.home), flipSq (sq 6 p.turn.home), none⟩
  rw [c3_flip_sq_home' 4 (by decide) p.turn, c3_flip_sq_home' 6 (by decide) p.turn]

theorem c3_mvQ (p : Pos) :
    (⟨sq 4 p.turn.opp.home, sq 2 p.turn.opp.home, none⟩ : Move) =
    flipMove ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ := by
  show (⟨sq 4 p.turn.opp.home, sq 2 p.turn.opp.home, none⟩ : Move) =
    ⟨flipSq (sq 4 p.turn.home), flipSq (sq 2 p.turn.home), none⟩
  rw [c3_flip_sq_home' 4 (by decide) p.turn, c3_flip_sq_home' 2 (by decide) p.turn]

theorem c3_castleMoves_flip (p : Pos) :
    castleMoves (flipPos p) = (castleMoves p).map flipMove := by
  have hb : (flipPos p).board = flipBoard p.board := rfl
  have hturn : (flipPos p).turn = p.turn.opp := rfl
  rw [castleMoves_eq (flipPos p), castleMoves_eq p, hb, hturn]
  rw [c3_kingHome_flip p p.turn, c3_attacked_home_flip p p.turn 4 (by decide),
    c3_castleK_flip p p.turn, c3_rookHome_flip p p.turn 7 (by decide),
    c3_all_empty_flip p [5, 6] p.turn (by decide),
    c3_attacked_home_flip p p.turn 5 (by decide),
    c3_castleQ_flip p p.turn, c3_rookHome_flip p p.turn 0 (by decide),
    c3_all_empty_flip p [1, 2, 3] p.turn (by decide),
    c3_attacked_home_flip p p.turn 3 (by decide)]
  rw [apply_ite (List.map flipMove), List.map_append,
    apply_ite (List.map flipMove), apply_ite (List.map flipMove)]
  rw [List.map_cons, List.map_nil, c3_mvK, c3_mvQ, List.map_cons, List.map_nil]

theorem mem_castleMoves_flip (p : Pos) (m : Move) :
    flipMove m ∈ castleMoves (flipPos p) ↔ m ∈ castleMoves p := by
  rw [c3_castleMoves_flip]
  exact c3_mem_flipMove m _

theorem c3_mem_pseudo_flip_le (p : Pos) (m : Move) (h : m ∈ pseudo p) :
    flipMove m ∈ pseudo (flipPos p) := by
  rw [pseudo_eq p, List.mem_append] at h
  rw [pseudo_eq (flipPos p), List.mem_append]
  rcases h with h | h
  · left
    rw [List.mem_flatMap] at h ⊢
    obtain ⟨s, -, hs⟩ := h
    refine ⟨flipSq s, List.mem_finRange _, ?_⟩
    show flipMove m ∈ (match (p.board (flipSq (flipSq s))).map flipPiece with
      | some q => if q.color == p.turn.opp then pieceMoves (flipPos p) (flipSq s) q else []
      | none => [])
    rw [flipSq_flipSq]
    cases hb : p.board s with
    | none =>
      rw [hb] at hs
      exact False.elim (List.not_mem_nil hs)
    | some q =>
      rw [hb] at hs
      change m ∈ (if q.color == p.turn then pieceMoves p s q else []) at hs
      show flipMove m ∈ (if (flipPiece q).color == p.turn.opp then
          pieceMoves (flipPos p) (flipSq s) (flipPiece q) else [])
      have hcol : ((flipPiece q).color == p.turn.opp) = (q.color == p.turn) := by
        rw [show (flipPiece q).color = q.color.opp from rfl, opp_beq_opp]
      by_cases hc : q.color == p.turn
      · rw [if_pos hc] at hs
        rw [hcol, if_pos hc]
        exact (mem_pieceMoves_flip p s q m).mpr hs
      · rw [if_neg hc] at hs
        exact False.elim (List.not_mem_nil hs)
  · right
    exact (mem_castleMoves_flip p m).mpr h

theorem mem_pseudo_flip (p : Pos) (m : Move) :
    flipMove m ∈ pseudo (flipPos p) ↔ m ∈ pseudo p := by
  constructor
  · intro h
    have h2 := c3_mem_pseudo_flip_le (flipPos p) (flipMove m) h
    rwa [flipMove_flipMove, flipPos_flipPos] at h2
  · intro h
    exact c3_mem_pseudo_flip_le p m h

theorem c3_pos_ext {p q : Pos} (hb : p.board = q.board) (ht : p.turn = q.turn)
    (hck : p.castleK = q.castleK) (hcq : p.castleQ = q.castleQ) (hep : p.ep = q.ep) :
    p = q := by
  obtain ⟨b₁, t₁, k₁, q₁, e₁⟩ := p
  obtain ⟨b₂, t₂, k₂, q₂, e₂⟩ := q
  subst hb; subst ht; subst hck; subst hcq; subst hep
  rfl

theorem c3_beq_flip_right (a b : Sq) : (a == flipSq b) = (flipSq a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have h2 := congrArg flipSq h
    rw [flipSq_flipSq] at h2
    exact h2
  · intro h
    have h2 := congrArg flipSq h
    rwa [flipSq_flipSq] at h2

theorem c3_beq_flip_left (a b : Sq) : (flipSq a == b) = (a == flipSq b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have h2 := congrArg flipSq h
    rwa [flipSq_flipSq] at h2
  · intro h
    have h2 := congrArg flipSq h
    rwa [flipSq_flipSq] at h2

theorem c3_beq_map_flipSq' (o : Option Sq) (s : Sq) :
    (o.map flipSq == some s) = (o == some (flipSq s)) := by
  have h := c3_beq_map_flipSq o (flipSq s)
  rwa [flipSq_flipSq] at h

theorem c3_any_kind_flip (o : Option Piece) (k : Kind) :
    ((o.map flipPiece).any fun q => q.kind == k) = (o.any fun q => q.kind == k) := by
  cases o with
  | none => rfl
  | some q =>
    obtain ⟨c₁, k₁⟩ := q
    rfl

theorem c3_rank2_beq (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ((7 - a + 2 == 7 - b) = (b + 2 == a)) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor <;> intro h <;> omega

theorem c3_midpoint (a b : Nat) (ha : a < 8) (hb : b < 8) (h : a + 2 = b ∨ b + 2 = a) :
    (7 - a + (7 - b)) / 2 = 7 - (a + b) / 2 := by
  rcases h with h | h <;> omega

theorem c3_moved_flip (o : Option Piece) (pr : Option Kind) :
    (match pr with
      | some k => (o.map flipPiece).map fun q : Piece => (⟨q.color, k⟩ : Piece)
      | none => o.map flipPiece) =
    (match pr with
      | some k => o.map fun q : Piece => (⟨q.color, k⟩ : Piece)
      | none => o).map flipPiece := by
  cases pr with
  | none => rfl
  | some k =>
    cases o with
    | none => rfl
    | some q =>
      obtain ⟨c₁, k₁⟩ := q
      rfl

theorem c3_victim_val' (a b : Sq) :
    (sq (flipSq b).file (flipSq a).rank : Sq) = flipSq (sq b.file a.rank) := by
  rw [flipSq_file, flipSq_rank, flipSq_sq b.file a.rank (file_lt _) (c3_rank_lt _)]

theorem c3_rook_val1' (a : Sq) :
    ((sq 7 (flipSq a).rank, sq 5 (flipSq a).rank) : Sq × Sq) =
    (flipSq (sq 7 a.rank), flipSq (sq 5 a.rank)) := by
  rw [flipSq_rank, flipSq_sq 7 a.rank (by decide) (c3_rank_lt _),
    flipSq_sq 5 a.rank (by decide) (c3_rank_lt _)]

theorem c3_rook_val0' (a : Sq) :
    ((sq 0 (flipSq a).rank, sq 3 (flipSq a).rank) : Sq × Sq) =
    (flipSq (sq 0 a.rank), flipSq (sq 3 a.rank)) := by
  rw [flipSq_rank, flipSq_sq 0 a.rank (by decide) (c3_rank_lt _),
    flipSq_sq 3 a.rank (by decide) (c3_rank_lt _)]

theorem c3_rook_case (b : Board) (s : Sq) (o : Option (Sq × Sq)) :
    (match o.map (fun x : Sq × Sq => (flipSq x.1, flipSq x.2)) with
      | some (a', d') => (if s == d' then flipBoard b a' else if s == a' then none
          else flipBoard b s : Option Piece)
      | none => flipBoard b s) =
    (match o with
      | some (a, d) => (if flipSq s == d then b a else if flipSq s == a then none
          else b (flipSq s) : Option Piece)
      | none => b (flipSq s)).map flipPiece := by
  cases o with
  | none => rfl
  | some pr =>
    obtain ⟨a, d⟩ := pr
    show (if s == flipSq d then flipBoard b (flipSq a) else if s == flipSq a then none
        else flipBoard b s) =
      (if flipSq s == d then b a else if flipSq s == a then none else b (flipSq s)).map flipPiece
    rw [apply_ite (Option.map flipPiece), apply_ite (Option.map flipPiece)]
    by_cases hd : flipSq s == d
    · have hd' : (s == flipSq d) = true := by rw [c3_beq_flip_right]; exact hd
      rw [if_pos hd', if_pos hd]
      show flipBoard b (flipSq a) = (b a).map flipPiece
      show (b (flipSq (flipSq a))).map flipPiece = (b a).map flipPiece
      rw [flipSq_flipSq]
    · have hd' : ¬(s == flipSq d) = true := by rw [c3_beq_flip_right]; exact hd
      rw [if_neg hd', if_neg hd]
      by_cases ha : flipSq s == a
      · have ha' : (s == flipSq a) = true := by rw [c3_beq_flip_right]; exact ha
        rw [if_pos ha', if_pos ha]
        rfl
      · have ha' : ¬(s == flipSq a) = true := by rw [c3_beq_flip_right]; exact ha
        rw [if_neg ha', if_neg ha]
        rfl

theorem play_flip (p : Pos) (m : Move) : play (flipPos p) (flipMove m) = flipPos (play p m) := by
  apply c3_pos_ext
  · funext s
    have hm1 : (flipMove m).src = flipSq m.src := rfl
    have hm2 : (flipMove m).dst = flipSq m.dst := rfl
    have hm3 : (flipMove m).promo = m.promo := rfl
    have hb : (flipPos p).board = flipBoard p.board := rfl
    show (if s == (flipMove m).dst then
          (match (flipMove m).promo with
          | some k => ((flipPos p).board (flipMove m).src).map fun q : Piece => (⟨q.color, k⟩ : Piece)
          | none => (flipPos p).board (flipMove m).src)
        else if (s == (flipMove m).src) ||
            ((if (((flipPos p).board (flipMove m).src).any fun q => q.kind == .pawn) &&
                ((flipMove m).src.file != (flipMove m).dst.file) &&
                empty (flipPos p).board (flipMove m).dst
              then some (sq (flipMove m).dst.file (flipMove m).src.rank : Sq)
              else none) == some s)
        then none
        else
          (match (if (((flipPos p).board (flipMove m).src).any fun q => q.kind == .king) &&
                (flipMove m).src.file + 2 == (flipMove m).dst.file
            then some (sq 7 (flipMove m).src.rank, sq 5 (flipMove m).src.rank)
            else if (((flipPos p).board (flipMove m).src).any fun q => q.kind == .king) &&
                (flipMove m).dst.file + 2 == (flipMove m).src.file
              then some (sq 0 (flipMove m).src.rank, sq 3 (flipMove m).src.rank)
              else none) with
          | some (a, d) => (if s == d then (flipPos p).board a else if s == a then none
              else (flipPos p).board s : Option Piece)
          | none => (flipPos p).board s)) =
      ((if flipSq s == m.dst then
          (match m.promo with
          | some k => (p.board m.src).map fun q : Piece => (⟨q.color, k⟩ : Piece)
          | none => p.board m.src)
        else if (flipSq s == m.src) ||
            ((if ((p.board m.src).any fun q => q.kind == .pawn) &&
                (m.src.file != m.dst.file) && empty p.board m.dst
              then some (sq m.dst.file m.src.rank : Sq)
              else none) == some (flipSq s))
        then none
        else
          (match (if ((p.board m.src).any fun q => q.kind == .king) &&
                m.src.file + 2 == m.dst.file
            then some (sq 7 m.src.rank, sq 5 m.src.rank)
            else if ((p.board m.src).any fun q => q.kind == .king) &&
                m.dst.file + 2 == m.src.file
              then some (sq 0 m.src.rank, sq 3 m.src.rank)
              else none) with
          | some (a, d) => (if flipSq s == d then p.board a else if flipSq s == a then none
              else p.board (flipSq s) : Option Piece)
          | none => p.board (flipSq s))).map flipPiece)
    rw [hm1, hm2, hm3, hb]
    have hsrcval : flipBoard p.board (flipSq m.src) = (p.board m.src).map flipPiece := by
      show (p.board (flipSq (flipSq m.src))).map flipPiece = _
      rw [flipSq_flipSq]
    rw [hsrcval]
    have hIsP : (((p.board m.src).map flipPiece).any fun q => q.kind == .pawn) =
        ((p.board m.src).any fun q => q.kind == .pawn) := c3_any_kind_flip _ _
    have hIsK : (((p.board m.src).map flipPiece).any fun q => q.kind == .king) =
        ((p.board m.src).any fun q => q.kind == .king) := c3_any_kind_flip _ _
    have hfd : ((flipSq m.src).file != (flipSq m.dst).file) = (m.src.file != m.dst.file) := by
      rw [flipSq_file, flipSq_file]
    have hemp : empty (flipBoard p.board) (flipSq m.dst) = empty p.board m.dst := empty_flip _ _
    rw [hIsP, hfd, hemp, hIsK]
    have hvv : (sq (flipSq m.dst).file (flipSq m.src).rank : Sq) = flipSq (sq m.dst.file m.src.rank) :=
      c3_victim_val' m.src m.dst
    have hf12 : ((flipSq m.src).file + 2 == (flipSq m.dst).file) = (m.src.file + 2 == m.dst.file) := by
      rw [flipSq_file, flipSq_file]
    have hf21 : ((flipSq m.dst).file + 2 == (flipSq m.src).file) = (m.dst.file + 2 == m.src.file) := by
      rw [flipSq_file, flipSq_file]
    have hrook : (if ((p.board m.src).any fun q => q.kind == .king) &&
          ((flipSq m.src).file + 2 == (flipSq m.dst).file)
        then (some (sq 7 (flipSq m.src).rank, sq 5 (flipSq m.src).rank) : Option (Sq × Sq))
        else if ((p.board m.src).any fun q => q.kind == .king) &&
            ((flipSq m.dst).file + 2 == (flipSq m.src).file)
          then some (sq 0 (flipSq m.src).rank, sq 3 (flipSq m.src).rank)
          else none) =
      ((if ((p.board m.src).any fun q => q.kind == .king) && (m.src.file + 2 == m.dst.file)
        then (some (sq 7 m.src.rank, sq 5 m.src.rank) : Option (Sq × Sq))
        else if ((p.board m.src).any fun q => q.kind == .king) && (m.dst.file + 2 == m.src.file)
          then some (sq 0 m.src.rank, sq 3 m.src.rank)
          else none).map fun x : Sq × Sq => (flipSq x.1, flipSq x.2)) := by
      rw [apply_ite (Option.map fun x : Sq × Sq => (flipSq x.1, flipSq x.2)),
        apply_ite (Option.map fun x : Sq × Sq => (flipSq x.1, flipSq x.2)),
        Option.map_some, Option.map_some, Option.map_none]
      rw [hf12, hf21, c3_rook_val1' m.src, c3_rook_val0' m.src]
    have hC2 : ((s == flipSq m.src) ||
        ((if ((p.board m.src).any fun q => q.kind == .pawn) && (m.src.file != m.dst.file) &&
            empty p.board m.dst
          then some (sq (flipSq m.dst).file (flipSq m.src).rank : Sq)
          else none) == some s)) =
      ((flipSq s == m.src) ||
        ((if ((p.board m.src).any fun q => q.kind == .pawn) && (m.src.file != m.dst.file) &&
            empty p.board m.dst
          then some (sq m.dst.file m.src.rank : Sq)
          else none) == some (flipSq s))) := by
      rw [c3_beq_flip_right]
      by_cases hC : ((p.board m.src).any (fun q => q.kind == .pawn) && (m.src.file != m.dst.file) &&
          empty p.board m.dst) = true
      · rw [if_pos hC, if_pos hC, hvv]
        have hsb : ((some (flipSq (sq m.dst.file m.src.rank)) : Option Sq) == some s) =
            ((some (sq m.dst.file m.src.rank)) == some (flipSq s)) := by
          show ((flipSq (sq m.dst.file m.src.rank)) == s) =
            (sq m.dst.file m.src.rank == flipSq s)
          exact c3_beq_flip_left _ s
        rw [hsb]
      · rw [if_neg hC, if_neg hC]
        rfl
    rw [c3_beq_flip_right s m.dst, hC2, hrook]
    rw [apply_ite (Option.map flipPiece), apply_ite (Option.map flipPiece)]
    have hmoved : (match m.promo with
        | some k => ((p.board m.src).map flipPiece).map fun q : Piece => (⟨q.color, k⟩ : Piece)
        | none => (p.board m.src).map flipPiece) =
      (match m.promo with
        | some k => (p.board m.src).map fun q : Piece => (⟨q.color, k⟩ : Piece)
        | none => p.board m.src).map flipPiece := c3_moved_flip _ _
    rw [hmoved, c3_rook_case]
    rfl
  · rfl
  · funext c
    show (p.castleK c.opp && !((flipSq m.src == sq 4 c.home) || (flipSq m.dst == sq 4 c.home)) &&
        !((flipSq m.src == sq 7 c.home) || (flipSq m.dst == sq 7 c.home))) =
      (p.castleK c.opp && !((m.src == sq 4 c.opp.home) || (m.dst == sq 4 c.opp.home)) &&
        !((m.src == sq 7 c.opp.home) || (m.dst == sq 7 c.opp.home)))
    have h4 : ((flipSq m.src == sq 4 c.home) || (flipSq m.dst == sq 4 c.home)) =
        ((m.src == sq 4 c.opp.home) || (m.dst == sq 4 c.opp.home)) := by
      rw [c3_beq_flip_left, c3_beq_flip_left,
        c3_flip_sq_home' 4 (by decide) c]
    have h7 : ((flipSq m.src == sq 7 c.home) || (flipSq m.dst == sq 7 c.home)) =
        ((m.src == sq 7 c.opp.home) || (m.dst == sq 7 c.opp.home)) := by
      rw [c3_beq_flip_left, c3_beq_flip_left,
        c3_flip_sq_home' 7 (by decide) c]
    rw [h4, h7]
  · funext c
    show (p.castleQ c.opp && !((flipSq m.src == sq 4 c.home) || (flipSq m.dst == sq 4 c.home)) &&
        !((flipSq m.src == sq 0 c.home) || (flipSq m.dst == sq 0 c.home))) =
      (p.castleQ c.opp && !((m.src == sq 4 c.opp.home) || (m.dst == sq 4 c.opp.home)) &&
        !((m.src == sq 0 c.opp.home) || (m.dst == sq 0 c.opp.home)))
    have h4 : ((flipSq m.src == sq 4 c.home) || (flipSq m.dst == sq 4 c.home)) =
        ((m.src == sq 4 c.opp.home) || (m.dst == sq 4 c.opp.home)) := by
      rw [c3_beq_flip_left, c3_beq_flip_left,
        c3_flip_sq_home' 4 (by decide) c]
    have h0 : ((flipSq m.src == sq 0 c.home) || (flipSq m.dst == sq 0 c.home)) =
        ((m.src == sq 0 c.opp.home) || (m.dst == sq 0 c.opp.home)) := by
      rw [c3_beq_flip_left, c3_beq_flip_left,
        c3_flip_sq_home' 0 (by decide) c]
    rw [h4, h0]
  · show (if ((flipPos p).board (flipMove m).src).any (fun q => q.kind == .pawn) &&
        (((flipMove m).src.rank + 2 == (flipMove m).dst.rank) ||
          ((flipMove m).dst.rank + 2 == (flipMove m).src.rank))
      then (some (sq (flipMove m).src.file (((flipMove m).src.rank + (flipMove m).dst.rank) / 2)) : Option Sq)
      else none) =
      ((if (p.board m.src).any (fun q => q.kind == .pawn) &&
        ((m.src.rank + 2 == m.dst.rank) || (m.dst.rank + 2 == m.src.rank))
      then some (sq m.src.file ((m.src.rank + m.dst.rank) / 2))
      else none).map flipSq)
    rw [apply_ite (Option.map flipSq), Option.map_some, Option.map_none]
    have hm1 : (flipMove m).src = flipSq m.src := rfl
    have hm2 : (flipMove m).dst = flipSq m.dst := rfl
    rw [hm1, hm2]
    have hIsP : ((flipPos p).board (flipSq m.src)).any (fun q => q.kind == .pawn) =
        (p.board m.src).any (fun q => q.kind == .pawn) := by
      show ((p.board (flipSq (flipSq m.src))).map flipPiece).any (fun q => q.kind == .pawn) = _
      rw [flipSq_flipSq]
      exact c3_any_kind_flip _ _
    have hr1 : ((7 - m.src.rank) + 2 == (7 - m.dst.rank)) = (m.dst.rank + 2 == m.src.rank) := by
      exact c3_rank2_beq m.src.rank m.dst.rank (c3_rank_lt _) (c3_rank_lt _)
    have hr2 : ((7 - m.dst.rank) + 2 == (7 - m.src.rank)) = (m.src.rank + 2 == m.dst.rank) := by
      exact c3_rank2_beq m.dst.rank m.src.rank (c3_rank_lt _) (c3_rank_lt _)
    have hsrcrk : (flipSq m.src).rank = 7 - m.src.rank := flipSq_rank m.src
    have hdstrk : (flipSq m.dst).rank = 7 - m.dst.rank := flipSq_rank m.dst
    rw [hIsP, flipSq_file, hsrcrk, hdstrk, hr1, hr2]
    have hdisj : ((m.dst.rank + 2 == m.src.rank) || (m.src.rank + 2 == m.dst.rank)) =
        ((m.src.rank + 2 == m.dst.rank) || (m.dst.rank + 2 == m.src.rank)) := Bool.or_comm _ _
    rw [hdisj]
    by_cases hC : ((p.board m.src).any (fun q => q.kind == .pawn) &&
        ((m.src.rank + 2 == m.dst.rank) || (m.dst.rank + 2 == m.src.rank))) = true
    · rw [if_pos hC, if_pos hC]
      have hmidlt : (m.src.rank + m.dst.rank) / 2 < 8 := by
        have h1 := c3_rank_lt m.src
        have h2 := c3_rank_lt m.dst
        omega
      rw [flipSq_sq m.src.file ((m.src.rank + m.dst.rank) / 2) (file_lt _) hmidlt]
      apply congrArg (fun x => some (sq m.src.file x))
      have hpm : m.dst.rank + 2 = m.src.rank ∨ m.src.rank + 2 = m.dst.rank := by
        rw [Bool.and_eq_true] at hC
        rcases (Bool.or_eq_true _ _).mp hC.2 with h | h
        · exact Or.inr (beq_iff_eq.mp h)
        · exact Or.inl (beq_iff_eq.mp h)
      rcases hpm with hpm | hpm
      · exact c3_midpoint m.src.rank m.dst.rank (c3_rank_lt _) (c3_rank_lt _) (Or.inr hpm)
      · exact c3_midpoint m.src.rank m.dst.rank (c3_rank_lt _) (c3_rank_lt _) (Or.inl hpm)
    · rw [if_neg hC, if_neg hC]

theorem mem_legal_flip (p : Pos) (m : Move) : flipMove m ∈ legalMoves (flipPos p) ↔ m ∈ legalMoves p := by
  have ht : (flipPos p).turn = p.turn.opp := rfl
  have h := inCheck_flip (play p m) p.turn
  simp only [legalMoves, List.mem_filter]
  constructor
  · rintro ⟨hps, hs⟩
    refine ⟨(mem_pseudo_flip p m).mp hps, ?_⟩
    rw [play_flip, ht, h] at hs
    exact hs
  · rintro ⟨hps, hs⟩
    refine ⟨(mem_pseudo_flip p m).mpr hps, ?_⟩
    rw [play_flip, ht, h]
    exact hs

theorem givesCheck_flip (p : Pos) (m : Move) : givesCheck (flipPos p) (flipMove m) = givesCheck p m := by
  show inCheck (play (flipPos p) (flipMove m)) p.turn.opp.opp = inCheck (play p m) p.turn.opp
  rw [play_flip, inCheck_flip]

theorem length_legal_flip (p : Pos) : (legalMoves (flipPos p)).length = (legalMoves p).length := by
  apply Nat.le_antisymm
  · have hsub : legalMoves (flipPos p) ⊆ (legalMoves p).map flipMove := by
      intro m hm
      rw [List.mem_map]
      have hm' : flipMove (flipMove m) ∈ legalMoves (flipPos p) := by
        rw [flipMove_flipMove]
        exact hm
      exact ⟨flipMove m, (mem_legal_flip p (flipMove m)).mp hm', flipMove_flipMove m⟩
    have hnd : ((legalMoves p).map flipMove).Nodup :=
      nodup_map_of_inj (legalMoves_nodup p) fun x _ y _ h => flipMove_injective h
    have := List.Nodup.length_le_of_subset (legalMoves_nodup (flipPos p)) hsub
    rwa [List.length_map] at this
  · have hsub : (legalMoves p).map flipMove ⊆ legalMoves (flipPos p) := by
      intro m hm
      rw [List.mem_map] at hm
      obtain ⟨m₀, hm₀, rfl⟩ := hm
      exact (mem_legal_flip p m₀).mpr hm₀
    have hnd : ((legalMoves p).map flipMove).Nodup :=
      nodup_map_of_inj (legalMoves_nodup p) fun x _ y _ h => flipMove_injective h
    have := List.Nodup.length_le_of_subset hnd hsub
    rwa [List.length_map] at this

theorem allCheck_flip (p : Pos) (h : AllCheck p) : AllCheck (flipPos p) := by
  intro m hm
  have hm' : flipMove (flipMove m) ∈ legalMoves (flipPos p) := by
    rw [flipMove_flipMove]
    exact hm
  have h0 := h (flipMove m) ((mem_legal_flip p (flipMove m)).mp hm')
  have hg := givesCheck_flip p (flipMove m)
  rw [flipMove_flipMove] at hg
  rw [hg]
  exact h0

theorem reduce_white (P : Pos → Prop) (hP : ∀ p, P p → P (flipPos p))
    (hW : ∀ p, P p → p.turn = .white → (legalMoves p).length ≤ 63) :
    ∀ p, P p → (legalMoves p).length ≤ 63 := by
  intro p hp
  cases ht : p.turn with
  | white => exact hW p hp ht
  | black =>
    rw [← length_legal_flip]
    exact hW _ (hP p hp) (by simp [flipPos, ht, Color.opp])

end Chess.All63
