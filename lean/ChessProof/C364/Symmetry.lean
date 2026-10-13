import ChessProof.C364.Chains
import ChessProof.All63.Symmetry

namespace Chess.C364

open Chess

def noCastle (p : Pos) : Pos := { p with castleK := fun _ => false, castleQ := fun _ => false }

def mirrorMove (m : Move) : Move := { m with src := fileMirror m.src, dst := fileMirror m.dst }

def mirrorPos (p : Pos) : Pos where
  board s := p.board (fileMirror s)
  turn := p.turn
  castleK _ := false
  castleQ _ := false
  ep := p.ep.map fileMirror

def swapPiece (q : Piece) : Piece := ⟨q.color.opp, q.kind⟩

def swapMove (m : Move) : Move := { m with src := rankMirror m.src, dst := rankMirror m.dst }

def swapPos (p : Pos) : Pos where
  board s := (p.board (rankMirror s)).map swapPiece
  turn := p.turn.opp
  castleK _ := false
  castleQ _ := false
  ep := p.ep.map rankMirror

theorem play_noCastle (p : Pos) (m : Move) : play (noCastle p) m = noCastle (play p m) := by
  rfl

theorem kf_noCastle (p : Pos) (ms : List Move) :
    KFChain p ms ↔ KFChain (noCastle p) ms := by
  induction ms generalizing p with
  | nil => exact Iff.rfl
  | cons m ms ih =>
    constructor
    · rintro ⟨hl, hg, hk, hrest⟩
      refine ⟨?_, hg, hk, ?_⟩
      · exact (legal_castleRights_indep p m hk (fun _ => false) (fun _ => false)).mp hl
      · rw [play_noCastle]
        exact (ih (play p m)).mp hrest
    · rintro ⟨hl, hg, hk, hrest⟩
      refine ⟨?_, hg, hk, ?_⟩
      · exact (legal_castleRights_indep p m hk (fun _ => false) (fun _ => false)).mpr hl
      · rw [play_noCastle] at hrest
        exact (ih (play p m)).mpr hrest

theorem caps_noCastle (p : Pos) (ms : List Move) : caps (noCastle p) ms = caps p ms := by
  induction ms generalizing p with
  | nil => rfl
  | cons m ms ih =>
    show ((if isCapture (noCastle p) m then 1 else 0) + caps (play (noCastle p) m) ms) =
      (if isCapture p m then 1 else 0) + caps (play p m) ms
    have hc : (if isCapture (noCastle p) m then (1 : Nat) else 0) =
        if isCapture p m then 1 else 0 := rfl
    rw [play_noCastle, hc, ih (play p m)]

theorem c0_noCastle (p : Pos) (h : C0 p) : C0 (noCastle p) :=
  ⟨h.wk, h.bk, h.apart, h.pawns, h.safe, h.ep⟩

theorem fileMirror_injective : Function.Injective fileMirror := by
  intro a b h
  have h2 := congrArg fileMirror h
  rwa [fileMirror_invol, fileMirror_invol] at h2

theorem mem_fileMirror_map {l : List Sq} {t : Sq} : fileMirror t ∈ l.map fileMirror ↔ t ∈ l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨u, hu, hu2⟩
    rwa [fileMirror_injective hu2] at hu
  · intro h
    exact ⟨t, h, rfl⟩

theorem beq_fileMirror (v u : Sq) : (fileMirror v == fileMirror u) = (v == u) := by
  by_cases h : v = u
  · subst h
    rw [beq_self_eq_true, beq_self_eq_true]
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (fun hh => h (fileMirror_injective hh))]

theorem beq_ep_mirror (e : Option Sq) (u : Sq) :
    (e.map fileMirror == some (fileMirror u)) = (e == some u) := by
  cases e with
  | none => rfl
  | some v =>
    show (some (fileMirror v) == some (fileMirror u)) = (some v == some u)
    change (fileMirror v == fileMirror u) = (v == u)
    exact beq_fileMirror v u

theorem empty_mirror (b : Board) (t : Sq) :
    empty (fun z => b (fileMirror z)) (fileMirror t) = empty b t := by
  show (b (fileMirror (fileMirror t))).isNone = (b t).isNone
  rw [fileMirror_invol]

theorem foe_mirror (b : Board) (c : Color) (u : Sq) :
    foe (fun z => b (fileMirror z)) c (fileMirror u) = foe b c u := by
  show (match b (fileMirror (fileMirror u)) with
      | some q => q.color != c
      | none => false) = _
  rw [fileMirror_invol]
  rfl

theorem mkSq_mirror (f r : Nat) (hf : f < 8) : mkSq (7 - f) r = (mkSq f r).map fileMirror := by
  by_cases hr : r < 8
  · have h1 : r * 8 + f < 64 := by omega
    have h2 : (r * 8 + f) / 8 = r := by omega
    have h3 : (r * 8 + f) % 8 = f := by omega
    simp only [mkSq]
    rw [dif_pos ⟨by omega, hr⟩, dif_pos ⟨hf, hr⟩]
    apply congrArg some
    apply Fin.ext
    show r * 8 + (7 - f) = (r * 8 + f) / 8 * 8 + (7 - (r * 8 + f) % 8)
    rw [h2, h3]
  · simp only [mkSq]
    rw [dif_neg (by omega), dif_neg (by omega), Option.map_none]

theorem off_mirror_aux (sf sr df dr : Int) :
    (if 0 ≤ 7 - sf + -df ∧ 0 ≤ sr + dr then mkSq (7 - sf + -df).toNat (sr + dr).toNat else none) =
    (if 0 ≤ sf + df ∧ 0 ≤ sr + dr then mkSq (sf + df).toNat (sr + dr).toNat else none).map
      fileMirror := by
  by_cases hP : 0 ≤ sf + df
  · by_cases hQ : 0 ≤ sr + dr
    · by_cases hP7 : sf + df < 8
      · rw [if_pos ⟨by omega, hQ⟩, if_pos ⟨hP, hQ⟩]
        have htf : (7 - sf + -df).toNat = 7 - (sf + df).toNat := by omega
        rw [htf]
        exact mkSq_mirror _ _ (by omega)
      · rw [if_neg (by omega), if_pos ⟨hP, hQ⟩]
        simp only [mkSq]
        rw [dif_neg (by omega), Option.map_none]
    · rw [if_neg (by omega), if_neg (by omega), Option.map_none]
  · by_cases hC : 0 ≤ 7 - sf + -df ∧ 0 ≤ sr + dr
    · rw [if_pos hC, if_neg (by omega)]
      simp only [mkSq]
      rw [dif_neg (by omega), Option.map_none]
    · rw [if_neg hC, if_neg (by omega), Option.map_none]

theorem off_mirror (s : Sq) (df dr : Int) : off (fileMirror s) (-df) dr = (off s df dr).map fileMirror := by
  have hfm : ((fileMirror s).file : Int) = 7 - (s.file : Int) := (fileMirror_coords s).1
  have hrm : ((fileMirror s).rank : Int) = (s.rank : Int) := (fileMirror_coords s).2
  simp only [off]
  rw [hfm, hrm]
  exact off_mirror_aux (s.file : Int) (s.rank : Int) df dr

theorem off_mirror_eq (s t : Sq) (df dr : Int) :
    off (fileMirror s) df dr = some (fileMirror t) ↔ off s (-df) dr = some t := by
  have h := off_mirror s (-df) dr
  rw [Int.neg_neg] at h
  rw [h, Option.map_eq_some_iff]
  constructor
  · rintro ⟨u, hu, hu2⟩
    rwa [fileMirror_injective hu2] at hu
  · intro ht
    exact ⟨t, ht, rfl⟩

theorem ray_mirror (b : Board) (s : Sq) (df dr : Int) (n : Nat) :
    ray (fun z => b (fileMirror z)) (fileMirror s) (-df) dr n =
    (ray b s df dr n).map fileMirror := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show (match off (fileMirror s) (-df) dr with
      | none => []
      | some t => if empty (fun z => b (fileMirror z)) t then
          t :: ray (fun z => b (fileMirror z)) t (-df) dr n else [t]) =
      (match off s df dr with
      | none => []
      | some t => if empty b t then t :: ray b t df dr n else [t]).map fileMirror
    rw [off_mirror]
    cases h : off s df dr with
    | none => rfl
    | some t =>
      rw [Option.map_some]
      show (if empty (fun z => b (fileMirror z)) (fileMirror t) then
          fileMirror t :: ray (fun z => b (fileMirror z)) (fileMirror t) (-df) dr n
        else [fileMirror t]) =
        (if empty b t then t :: ray b t df dr n else [t]).map fileMirror
      rw [empty_mirror]
      by_cases he : empty b t
      · rw [if_pos he, if_pos he, ih t]
        rfl
      · rw [if_neg he, if_neg he]
        rfl

theorem mem_ray_mirror (b : Board) (s t : Sq) (df dr : Int) (n : Nat) :
    fileMirror t ∈ ray (fun z => b (fileMirror z)) (fileMirror s) df dr n ↔
    t ∈ ray b s (-df) dr n := by
  have h := ray_mirror b s (-df) dr n
  rw [Int.neg_neg] at h
  rw [h]
  exact mem_fileMirror_map

theorem mem_steps_mirror (s t : Sq) (ds : List (Int × Int)) :
    fileMirror t ∈ steps (fileMirror s) ds ↔ t ∈ steps s (ds.map fun d => (-d.1, d.2)) := by
  simp only [steps, List.mem_filterMap, List.mem_map]
  constructor
  · rintro ⟨d, hd, hoff⟩
    exact ⟨(-d.1, d.2), ⟨d, hd, rfl⟩, (off_mirror_eq s t d.1 d.2).mp hoff⟩
  · rintro ⟨y, ⟨d, hd, rfl⟩, hoff⟩
    exact ⟨d, hd, (off_mirror_eq s t d.1 d.2).mpr hoff⟩

theorem mem_rays_mirror (b : Board) (s t : Sq) (ds : List (Int × Int)) :
    fileMirror t ∈ rays (fun z => b (fileMirror z)) (fileMirror s) ds ↔
    t ∈ rays b s (ds.map fun d => (-d.1, d.2)) := by
  simp only [rays, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨d, hd, hray⟩
    exact ⟨(-d.1, d.2), ⟨d, hd, rfl⟩, (mem_ray_mirror b s t d.1 d.2 7).mp hray⟩
  · rintro ⟨y, ⟨d, hd, rfl⟩, hray⟩
    exact ⟨d, hd, (mem_ray_mirror b s t d.1 d.2 7).mpr hray⟩

theorem knightD_negf_perm : List.Perm (knightD.map fun d => (-d.1, d.2)) knightD := by decide

theorem bishopD_negf_perm : List.Perm (bishopD.map fun d => (-d.1, d.2)) bishopD := by decide

theorem rookD_negf_perm : List.Perm (rookD.map fun d => (-d.1, d.2)) rookD := by decide

theorem queenD_negf_perm : List.Perm (queenD.map fun d => (-d.1, d.2)) queenD := by decide

theorem pawnD_negf_perm (c : Color) :
    List.Perm ([(1, c.fwd), (-1, c.fwd)].map fun d => (-d.1, d.2)) [(1, c.fwd), (-1, c.fwd)] := by
  cases c <;> decide

theorem mem_steps_of_perm {ds₁ ds₂ : List (Int × Int)} (h : List.Perm ds₁ ds₂) (s t : Sq) :
    t ∈ steps s ds₁ ↔ t ∈ steps s ds₂ := by
  simp only [steps, List.mem_filterMap]
  exact exists_congr fun d => and_congr h.mem_iff Iff.rfl

theorem mem_rays_of_perm {ds₁ ds₂ : List (Int × Int)} (h : List.Perm ds₁ ds₂) (b : Board) (s t : Sq) :
    t ∈ rays b s ds₁ ↔ t ∈ rays b s ds₂ := by
  simp only [rays, List.mem_flatMap]
  exact exists_congr fun d => and_congr h.mem_iff Iff.rfl

theorem attacks_mirror (b : Board) (s t : Sq) (q : Piece) :
    fileMirror t ∈ attacks (fun z => b (fileMirror z)) (fileMirror s) q ↔ t ∈ attacks b s q := by
  obtain ⟨c, k⟩ := q
  cases k
  case pawn =>
    show fileMirror t ∈ steps (fileMirror s) [(1, c.fwd), (-1, c.fwd)] ↔
      t ∈ steps s [(1, c.fwd), (-1, c.fwd)]
    exact (mem_steps_mirror s t _).trans (mem_steps_of_perm (pawnD_negf_perm c) s t)
  case knight =>
    show fileMirror t ∈ steps (fileMirror s) knightD ↔ t ∈ steps s knightD
    exact (mem_steps_mirror s t _).trans (mem_steps_of_perm knightD_negf_perm s t)
  case bishop =>
    show fileMirror t ∈ rays (fun z => b (fileMirror z)) (fileMirror s) bishopD ↔
      t ∈ rays b s bishopD
    exact (mem_rays_mirror b s t _).trans (mem_rays_of_perm bishopD_negf_perm b s t)
  case rook =>
    show fileMirror t ∈ rays (fun z => b (fileMirror z)) (fileMirror s) rookD ↔ t ∈ rays b s rookD
    exact (mem_rays_mirror b s t _).trans (mem_rays_of_perm rookD_negf_perm b s t)
  case queen =>
    show fileMirror t ∈ rays (fun z => b (fileMirror z)) (fileMirror s) queenD ↔ t ∈ rays b s queenD
    exact (mem_rays_mirror b s t _).trans (mem_rays_of_perm queenD_negf_perm b s t)
  case king =>
    show fileMirror t ∈ steps (fileMirror s) queenD ↔ t ∈ steps s queenD
    exact (mem_steps_mirror s t _).trans (mem_steps_of_perm queenD_negf_perm s t)

theorem attacked_mirror_le (b : Board) (s : Sq) (c : Color) (h : attacked b s c = true) :
    attacked (fun z => b (fileMirror z)) (fileMirror s) c = true := by
  unfold attacked at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨t, -, h⟩ := h
  refine ⟨fileMirror t, List.mem_finRange _, ?_⟩
  have hb : (fun z => b (fileMirror z)) (fileMirror t) = b t := by
    show b (fileMirror (fileMirror t)) = b t
    rw [fileMirror_invol]
  rw [hb]
  cases hbt : b t with
  | none =>
    rw [hbt] at h
    exact Bool.noConfusion h
  | some q =>
    rw [hbt] at h
    change (q.color == c && (attacks b t q).contains s) = true at h
    show (q.color == c && (attacks (fun z => b (fileMirror z)) (fileMirror t) q).contains
      (fileMirror s)) = true
    rw [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    rw [List.contains_eq_mem] at h ⊢
    exact decide_eq_true (attacks_mirror b t s q |>.mpr (of_decide_eq_true h.2))

theorem attacked_mirror (b : Board) (s : Sq) (c : Color) :
    attacked (fun z => b (fileMirror z)) (fileMirror s) c = attacked b s c := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    have h2 := attacked_mirror_le (fun z => b (fileMirror z)) (fileMirror s) c h
    simp only [fileMirror_invol] at h2
    exact h2
  · intro h
    exact attacked_mirror_le b s c h

theorem inCheck_mirror_le (p : Pos) (c : Color) (h : inCheck p c = true) :
    inCheck (mirrorPos p) c = true := by
  unfold inCheck at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨t, -, h⟩ := h
  refine ⟨fileMirror t, List.mem_finRange _, ?_⟩
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨hk, ha⟩ := h
  constructor
  · have hbt : p.board t = some ⟨c, .king⟩ := beq_iff_eq.mp hk
    have hb : (mirrorPos p).board (fileMirror t) = p.board t := by
      show p.board (fileMirror (fileMirror t)) = p.board t
      rw [fileMirror_invol]
    rw [hb, hbt]
    exact beq_iff_eq.mpr rfl
  · show attacked (fun z => p.board (fileMirror z)) (fileMirror t) c.opp = true
    exact attacked_mirror_le p.board t c.opp ha

theorem inCheck_mirror (p : Pos) (c : Color) : inCheck (mirrorPos p) c = inCheck p c := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    unfold inCheck at h ⊢
    rw [List.any_eq_true] at h ⊢
    obtain ⟨k, -, h⟩ := h
    rw [Bool.and_eq_true] at h
    obtain ⟨hk, ha⟩ := h
    refine ⟨fileMirror k, List.mem_finRange _, ?_⟩
    rw [Bool.and_eq_true]
    constructor
    · have hb : (mirrorPos p).board k = p.board (fileMirror k) := rfl
      rw [hb] at hk
      exact hk
    · show attacked p.board (fileMirror k) c.opp = true
      have h2 := attacked_mirror p.board (fileMirror k) c.opp
      simp only [fileMirror_invol] at h2
      rw [← h2]
      exact ha
  · intro h
    exact inCheck_mirror_le p c h

theorem rank_fileMirror (s : Sq) : (fileMirror s).rank = s.rank := by
  have h : ((fileMirror s).rank : Int) = (s.rank : Int) := (fileMirror_coords s).2
  have hlt : (fileMirror s).rank < 8 := by
    have := (fileMirror s).isLt
    show (fileMirror s).val / 8 < 8
    omega
  have hlt2 : s.rank < 8 := by
    have := s.isLt
    show s.val / 8 < 8
    omega
  omega

theorem file_fileMirror (s : Sq) : (fileMirror s).file = 7 - s.file := by
  have h : ((fileMirror s).file : Int) = 7 - (s.file : Int) := (fileMirror_coords s).1
  have hlt : s.file < 8 := Nat.mod_lt _ (by decide)
  have hlt2 : (fileMirror s).file < 8 := Nat.mod_lt _ (by decide)
  omega

theorem sq_mirror (f r : Nat) (hf : f < 8) (hr : r < 8) :
    fileMirror (sq f r) = sq (7 - f) r := by
  apply Fin.ext
  show ((r * 8 + f) % 64) / 8 * 8 + (7 - ((r * 8 + f) % 64) % 8) = (r * 8 + (7 - f)) % 64
  omega

theorem beq_mirror (s t : Sq) : (fileMirror s == t) = (s == fileMirror t) := by
  by_cases h : s = fileMirror t
  · have h2 : fileMirror s = t := by
      have h3 := congrArg fileMirror h
      rwa [fileMirror_invol] at h3
    rw [beq_iff_eq.mpr h2, beq_iff_eq.mpr h]
  · have h2 : fileMirror s ≠ t := by
      intro hh
      apply h
      have h3 := congrArg fileMirror hh
      rwa [fileMirror_invol] at h3
    rw [beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h]

theorem beq_mirror' (z t : Sq) : (z == fileMirror t) = (fileMirror z == t) := by
  by_cases h : z = fileMirror t
  · subst h
    rw [beq_self_eq_true, fileMirror_invol, beq_self_eq_true]
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr]
    intro hc
    apply h
    have h2 := congrArg fileMirror hc
    rwa [fileMirror_invol] at h2

theorem beq_map_mirror (e : Option Sq) (z : Sq) :
    (e.map fileMirror == some z) = (e == some (fileMirror z)) := by
  cases e with
  | none => rfl
  | some v =>
    show (some (fileMirror v) == some z) = (some v == some (fileMirror z))
    change (fileMirror v == z) = (v == fileMirror z)
    exact beq_mirror v z

theorem isKingMove_mirror (p : Pos) (m : Move) :
    isKingMove (mirrorPos p) (mirrorMove m) = isKingMove p m := by
  show (p.board (fileMirror (fileMirror m.src))).any (·.kind == .king) = _
  rw [fileMirror_invol]
  rfl

theorem pawnAny_mirror (p : Pos) (m : Move) :
    ((mirrorPos p).board (mirrorMove m).src).any (·.kind == .pawn) =
    (p.board m.src).any (·.kind == .pawn) := by
  show (p.board (fileMirror (fileMirror m.src))).any (·.kind == .pawn) = _
  rw [fileMirror_invol]

theorem isCastle_mirror (p : Pos) (m : Move) :
    isCastle (mirrorPos p) (mirrorMove m) = isCastle p m := by
  show (isKingMove (mirrorPos p) (mirrorMove m) &&
      ((fileMirror m.src).file + 2 == (fileMirror m.dst).file ||
        (fileMirror m.dst).file + 2 == (fileMirror m.src).file)) = _
  rw [isKingMove_mirror]
  have e1 : ((fileMirror m.src).file + 2 == (fileMirror m.dst).file) =
      (m.dst.file + 2 == m.src.file) := by
    rw [file_fileMirror, file_fileMirror]
    have h1 : m.src.file < 8 := Nat.mod_lt _ (by decide)
    have h2 : m.dst.file < 8 := Nat.mod_lt _ (by decide)
    cases h : (m.dst.file + 2 == m.src.file)
    · rw [beq_eq_false_iff_ne] at h ⊢
      intro hcontra
      apply h
      omega
    · rw [beq_iff_eq] at h ⊢
      omega
  have e2 : ((fileMirror m.dst).file + 2 == (fileMirror m.src).file) =
      (m.src.file + 2 == m.dst.file) := by
    rw [file_fileMirror, file_fileMirror]
    have h1 : m.src.file < 8 := Nat.mod_lt _ (by decide)
    have h2 : m.dst.file < 8 := Nat.mod_lt _ (by decide)
    cases h : (m.src.file + 2 == m.dst.file)
    · rw [beq_eq_false_iff_ne] at h ⊢
      intro hcontra
      apply h
      omega
    · rw [beq_iff_eq] at h ⊢
      omega
  rw [e1, e2]
  rw [Bool.or_comm]
  rfl

theorem epCap_mirror (p : Pos) (c : Color) (u : Sq) :
    epCap (mirrorPos p) c (fileMirror u) = epCap p c u := by
  show (p.ep.map fileMirror == some (fileMirror u) && empty (mirrorPos p).board (fileMirror u) &&
      match off (fileMirror u) 0 (-c.fwd) with
      | some v => p.board (fileMirror v) == some ⟨c.opp, Kind.pawn⟩
      | none => false) =
    (p.ep == some u && empty p.board u &&
      match off u 0 (-c.fwd) with
      | some v => p.board v == some ⟨c.opp, Kind.pawn⟩
      | none => false)
  rw [beq_ep_mirror]
  have ee : empty (mirrorPos p).board (fileMirror u) = empty p.board u := empty_mirror p.board u
  rw [ee]
  rw [show off (fileMirror u) 0 (-c.fwd) = (off u 0 (-c.fwd)).map fileMirror from off_mirror u 0 (-c.fwd)]
  cases h : off u 0 (-c.fwd) with
  | none => rfl
  | some v =>
    rw [Option.map_some]
    show (p.ep == some u && empty p.board u &&
        (p.board (fileMirror (fileMirror v)) == some ⟨c.opp, Kind.pawn⟩)) = _
    rw [fileMirror_invol]

theorem filter_mirror_eval (p g : Sq → Bool) (o : Option Sq) (h : ∀ a, p (fileMirror a) = g a) :
    (o.map fileMirror).filter p = (o.filter g).map fileMirror := by
  cases o with
  | none => rfl
  | some a =>
    rw [Option.map_some]
    rw [show (some (fileMirror a) : Option Sq).filter p =
        (if p (fileMirror a) then some (fileMirror a) else none) from rfl]
    rw [show (some a : Option Sq).filter g = (if g a then some a else none) from rfl]
    rw [h a]
    cases g a
    · rfl
    · rfl

theorem toList_map_mirror (o : Option Sq) : (o.map fileMirror).toList = o.toList.map fileMirror := by
  cases o <;> rfl

theorem board_empty_eq (p : Pos) :
    empty (mirrorPos p).board = fun z => empty p.board (fileMirror z) := funext fun z => rfl

theorem mem_one_mirror (p : Pos) (s t : Sq) (c : Color) :
    t ∈ ((off (fileMirror s) 0 c.fwd).filter (empty (mirrorPos p).board)).toList ↔
    ∃ u, u ∈ ((off s 0 c.fwd).filter (empty p.board)).toList ∧ fileMirror u = t := by
  rw [board_empty_eq]
  rw [show off (fileMirror s) 0 c.fwd = (off s 0 c.fwd).map fileMirror from off_mirror s 0 c.fwd]
  rw [filter_mirror_eval (fun z => empty p.board (fileMirror z)) (empty p.board) _
      (fun a => empty_mirror p.board a :
        ∀ a, (fun z => empty p.board (fileMirror z)) (fileMirror a) = empty p.board a),
    toList_map_mirror, List.mem_map]

theorem foe_mirror_t (p : Pos) (c : Color) (t : Sq) :
    foe (mirrorPos p).board c t = foe p.board c (fileMirror t) := by
  have h := foe_mirror p.board c (fileMirror t)
  simp only [fileMirror_invol] at h
  exact h

theorem epCap_mirror_t (p : Pos) (c : Color) (t : Sq) :
    epCap (mirrorPos p) c t = epCap p c (fileMirror t) := by
  have h := epCap_mirror p c (fileMirror t)
  simp only [fileMirror_invol] at h
  exact h

theorem pawnCaps_perm (c : Color) :
    List.Perm [(-1, c.fwd), (1, c.fwd)] [(1, c.fwd), (-1, c.fwd)] := by
  cases c <;> decide

theorem mem_caps_mirror (p : Pos) (s t : Sq) (c : Color) :
    t ∈ (steps (fileMirror s) [(1, c.fwd), (-1, c.fwd)]).filter
        (fun t => foe (mirrorPos p).board c t || epCap (mirrorPos p) c t) ↔
    ∃ u, u ∈ (steps s [(1, c.fwd), (-1, c.fwd)]).filter
        (fun t => foe p.board c t || epCap p c t) ∧ fileMirror u = t := by
  constructor
  · intro h
    rw [List.mem_filter] at h
    obtain ⟨hst, hG⟩ := h
    refine ⟨fileMirror t, ?_, fileMirror_invol t⟩
    rw [List.mem_filter]
    constructor
    · have h1 : fileMirror (fileMirror t) ∈ steps (fileMirror s) [(1, c.fwd), (-1, c.fwd)] := by
        rwa [fileMirror_invol]
      have h2 := (mem_steps_mirror s (fileMirror t) [(1, c.fwd), (-1, c.fwd)]).mp h1
      have h3 : ([(1, c.fwd), (-1, c.fwd)].map fun d : Int × Int => (-d.1, d.2)) =
          [(-1, c.fwd), (1, c.fwd)] := rfl
      rw [h3] at h2
      exact (mem_steps_of_perm (pawnCaps_perm c) s (fileMirror t)).mp h2
    · rw [Bool.or_eq_true] at hG ⊢
      rcases hG with hG | hG
      · exact Or.inl ((foe_mirror p.board c (fileMirror t)).symm.trans
          ((show t = fileMirror (fileMirror t) from (fileMirror_invol t).symm) ▸ hG))
      · exact Or.inr ((epCap_mirror p c (fileMirror t)).symm.trans
          ((show t = fileMirror (fileMirror t) from (fileMirror_invol t).symm) ▸ hG))
  · rintro ⟨u, h, rfl⟩
    rw [List.mem_filter] at h ⊢
    obtain ⟨hst, hG⟩ := h
    constructor
    · have h2 : u ∈ steps s ([(1, c.fwd), (-1, c.fwd)].map fun d : Int × Int => (-d.1, d.2)) :=
        (mem_steps_of_perm (pawnCaps_perm c) s u).mpr hst
      exact (mem_steps_mirror s u [(1, c.fwd), (-1, c.fwd)]).mpr h2
    · rw [Bool.or_eq_true] at hG ⊢
      rcases hG with hG | hG
      · exact Or.inl ((foe_mirror p.board c u).symm ▸ hG)
      · exact Or.inr ((epCap_mirror p c u).symm ▸ hG)

theorem mk_mirror (a b : Sq) (pr : Option Kind) :
    mirrorMove (Move.mk a b pr) = ⟨fileMirror a, fileMirror b, pr⟩ := rfl

theorem mem_mk_mirror (s t : Sq) (c : Color) (m : Move) :
    mirrorMove m ∈ (if (fileMirror t).rank == c.last then
        [Kind.knight, .bishop, .rook, .queen].map fun k => (⟨fileMirror s, fileMirror t, some k⟩ : Move)
      else [(⟨fileMirror s, fileMirror t, none⟩ : Move)]) ↔
    m ∈ (if t.rank == c.last then
        [Kind.knight, .bishop, .rook, .queen].map fun k => (⟨s, t, some k⟩ : Move)
      else [(⟨s, t, none⟩ : Move)]) := by
  rw [rank_fileMirror]
  by_cases hL : (t.rank == c.last) = true
  · rw [if_pos hL, if_pos hL]
    constructor
    · intro h
      rw [List.mem_map] at h ⊢
      obtain ⟨k, hk, hmeq⟩ := h
      refine ⟨k, hk, ?_⟩
      obtain ⟨ms, md, mp⟩ := m
      rw [mk_mirror] at hmeq
      have ha : s = ms := fileMirror_injective (congrArg Move.src hmeq)
      have hb : t = md := fileMirror_injective (congrArg Move.dst hmeq)
      have hc : some k = mp := congrArg Move.promo hmeq
      subst ha
      subst hb
      subst hc
      rfl
    · intro h
      rw [List.mem_map] at h ⊢
      obtain ⟨k, hk, hmeq⟩ := h
      refine ⟨k, hk, ?_⟩
      rw [← hmeq]
      show (⟨fileMirror s, fileMirror t, some k⟩ : Move) = mirrorMove (⟨s, t, some k⟩ : Move)
      rw [mk_mirror]
  · rw [if_neg hL, if_neg hL, List.mem_singleton, List.mem_singleton]
    constructor
    · intro hmeq
      obtain ⟨ms, md, mp⟩ := m
      rw [mk_mirror] at hmeq
      have ha : s = ms := fileMirror_injective (congrArg Move.src hmeq).symm
      have hb : t = md := fileMirror_injective (congrArg Move.dst hmeq).symm
      have hc : none = mp := (congrArg Move.promo hmeq).symm
      subst ha
      subst hb
      subst hc
      rfl
    · intro hmeq
      rw [hmeq, mk_mirror]

theorem pieceMoves_mirror_nonpawn (p : Pos) (s : Sq) (q : Piece) (m : Move)
    (hk : q.kind ≠ .pawn) :
    mirrorMove m ∈ pieceMoves (mirrorPos p) (fileMirror s) q ↔ m ∈ pieceMoves p s q := by
  rw [Chess.All63.pieceMoves_eq_of_nonpawn p s q hk,
    Chess.All63.pieceMoves_eq_of_nonpawn (mirrorPos p) (fileMirror s) q hk]
  rw [List.mem_map, List.mem_map]
  constructor
  · rintro ⟨t0, ht, hmeq⟩
    rw [List.mem_filter] at ht
    obtain ⟨hatt, ht2⟩ := ht
    obtain ⟨ms, md, mp⟩ := m
    rw [mk_mirror] at hmeq
    have ha : s = ms := fileMirror_injective (congrArg Move.src hmeq)
    have hb : t0 = fileMirror md := congrArg Move.dst hmeq
    have hc : mp = none := (congrArg Move.promo hmeq).symm
    subst hb
    subst ha
    subst hc
    refine ⟨md, ?_, rfl⟩
    rw [List.mem_filter]
    constructor
    · exact (attacks_mirror p.board s md q).mp hatt
    · show (!(p.board md).any (·.color == q.color)) = true
      rw [show ((mirrorPos p).board (fileMirror md)).any (·.color == q.color) =
          (p.board md).any (·.color == q.color) from by
        show (p.board (fileMirror (fileMirror md))).any (·.color == q.color) = _
        rw [fileMirror_invol]] at ht2
      exact ht2
  · rintro ⟨t0, ht, hmeq⟩
    rw [List.mem_filter] at ht
    obtain ⟨hatt, ht2⟩ := ht
    refine ⟨fileMirror t0, ?_, ?_⟩
    · rw [List.mem_filter]
      constructor
      · exact (attacks_mirror p.board s t0 q).mpr hatt
      · have h4 : ((mirrorPos p).board (fileMirror t0)).any (·.color == q.color) =
            (p.board t0).any (·.color == q.color) := by
          show (p.board (fileMirror (fileMirror t0))).any (·.color == q.color) = _
          rw [fileMirror_invol]
        rw [h4]
        exact ht2
    · show (⟨fileMirror s, fileMirror t0, none⟩ : Move) = mirrorMove m
      rw [← hmeq, mk_mirror]

theorem two_mirror (p : Pos) (s : Sq) (c : Color) :
    (if (fileMirror s).rank == c.pawnHome &&
        ((off (fileMirror s) 0 c.fwd).filter (empty (mirrorPos p).board)).isSome then
      (off (fileMirror s) 0 (2 * c.fwd)).filter (empty (mirrorPos p).board) else none) =
    (if s.rank == c.pawnHome && ((off s 0 c.fwd).filter (empty p.board)).isSome then
      (off s 0 (2 * c.fwd)).filter (empty p.board) else none).map fileMirror := by
  rw [rank_fileMirror]
  rw [board_empty_eq]
  have e0 : off (fileMirror s) 0 c.fwd = (off s 0 c.fwd).map fileMirror := off_mirror s 0 c.fwd
  have e0' : (off (fileMirror s) 0 c.fwd).filter (fun z => empty p.board (fileMirror z)) =
      ((off s 0 c.fwd).filter (empty p.board)).map fileMirror := by
    rw [e0]
    exact filter_mirror_eval (fun z => empty p.board (fileMirror z)) (empty p.board) _
      (fun a => empty_mirror p.board a :
        ∀ a, (fun z => empty p.board (fileMirror z)) (fileMirror a) = empty p.board a)
  rw [e0']
  have eis : (((off s 0 c.fwd).filter (empty p.board)).map fileMirror).isSome =
      ((off s 0 c.fwd).filter (empty p.board)).isSome := by
    cases (off s 0 c.fwd).filter (empty p.board) <;> rfl
  rw [eis]
  have e2 : (off (fileMirror s) 0 (2 * c.fwd)).filter (fun z => empty p.board (fileMirror z)) =
      ((off s 0 (2 * c.fwd)).filter (empty p.board)).map fileMirror := by
    rw [show off (fileMirror s) 0 (2 * c.fwd) = (off s 0 (2 * c.fwd)).map fileMirror from
      off_mirror s 0 (2 * c.fwd)]
    exact filter_mirror_eval (fun z => empty p.board (fileMirror z)) (empty p.board) _
      (fun a => empty_mirror p.board a :
        ∀ a, (fun z => empty p.board (fileMirror z)) (fileMirror a) = empty p.board a)
  rw [e2]
  split <;> rfl

theorem pieceMoves_mirror (p : Pos) (s : Sq) (q : Piece) (m : Move) :
    mirrorMove m ∈ pieceMoves (mirrorPos p) (fileMirror s) q ↔ m ∈ pieceMoves p s q := by
  obtain ⟨c, k⟩ := q
  cases k
  case pawn =>
    show mirrorMove m ∈ pawnMoves (mirrorPos p) (fileMirror s) c ↔ m ∈ pawnMoves p s c
    rw [Chess.All63.pawnMoves_eq, Chess.All63.pawnMoves_eq]
    constructor
    · intro h
      rw [List.mem_append] at h
      rcases h with h | h
      · rw [List.mem_flatMap] at h
        obtain ⟨t, ht, hmk⟩ := h
        rw [List.mem_append] at ht
        obtain ⟨u, hu, rfl⟩ : ∃ u, (u ∈ ((off s 0 c.fwd).filter (empty p.board)).toList ∨
            u ∈ (steps s [(1, c.fwd), (-1, c.fwd)]).filter fun t =>
              foe p.board c t || epCap p c t) ∧ fileMirror u = t := by
          rcases ht with ht | ht
          · obtain ⟨u, hu, hu2⟩ := (mem_one_mirror p s t c).mp ht
            exact ⟨u, Or.inl hu, hu2⟩
          · obtain ⟨u, hu, hu2⟩ := (mem_caps_mirror p s t c).mp ht
            exact ⟨u, Or.inr hu, hu2⟩
        have hmk2 := (mem_mk_mirror s u c m).mp hmk
        refine List.mem_append_left _ ?_
        rw [List.mem_flatMap]
        exact ⟨u, List.mem_append.mpr (by rcases hu with hu | hu; exact Or.inl hu; exact Or.inr hu),
          hmk2⟩
      · rw [List.mem_map] at h
        obtain ⟨t, ht, hmeq⟩ := h
        obtain ⟨u, hu, hu2⟩ : ∃ u, u ∈ ((if s.rank == c.pawnHome &&
            ((off s 0 c.fwd).filter (empty p.board)).isSome then
            (off s 0 (2 * c.fwd)).filter (empty p.board) else none).toList) ∧ fileMirror u = t := by
          rw [two_mirror, toList_map_mirror, List.mem_map] at ht
          exact ht
        refine List.mem_append_right _ ?_
        rw [List.mem_map]
        refine ⟨u, hu, ?_⟩
        obtain ⟨ms, md, mp⟩ := m
        rw [mk_mirror] at hmeq
        have ha : fileMirror s = fileMirror ms := congrArg Move.src hmeq
        have hb : t = fileMirror md := congrArg Move.dst hmeq
        have hc : none = mp := congrArg Move.promo hmeq
        have hsrc : s = ms := fileMirror_injective ha
        have hdst : u = md := fileMirror_injective (hu2.trans hb)
        subst hsrc
        subst hdst
        subst hc
        rfl
    · intro h
      rw [List.mem_append] at h
      rcases h with h | h
      · rw [List.mem_flatMap] at h
        obtain ⟨t, ht, hmk⟩ := h
        rw [List.mem_append] at ht
        refine List.mem_append_left _ ?_
        rw [List.mem_flatMap]
        refine ⟨fileMirror t, ?_, ?_⟩
        · rw [List.mem_append]
          rcases ht with ht | ht
          · exact Or.inl ((mem_one_mirror p s (fileMirror t) c).mpr ⟨t, ht, rfl⟩)
          · exact Or.inr ((mem_caps_mirror p s (fileMirror t) c).mpr ⟨t, ht, rfl⟩)
        · exact (mem_mk_mirror s t c m).mpr hmk
      · rw [List.mem_map] at h
        obtain ⟨t, ht, hmeq⟩ := h
        refine List.mem_append_right _ ?_
        rw [List.mem_map]
        refine ⟨fileMirror t, ?_, ?_⟩
        · rw [two_mirror, toList_map_mirror, List.mem_map]
          exact ⟨t, ht, rfl⟩
        · rw [show mirrorMove m = (⟨fileMirror m.src, fileMirror m.dst, m.promo⟩ : Move) from rfl,
            ← hmeq]
  all_goals exact pieceMoves_mirror_nonpawn p s ⟨c, _⟩ m (fun h => nomatch h)

theorem kdist_mirror (a b : Sq) : kdist (fileMirror a) (fileMirror b) = kdist a b := by
  obtain ⟨hf1, hr1⟩ := fileMirror_coords a
  obtain ⟨hf2, hr2⟩ := fileMirror_coords b
  show max ((fx (fileMirror a) - fx (fileMirror b)).natAbs)
      ((ry (fileMirror a) - ry (fileMirror b)).natAbs) =
    max ((fx a - fx b).natAbs) ((ry a - ry b).natAbs)
  rw [hf1, hr1, hf2, hr2]
  have e1 : (7 - fx a - (7 - fx b) : Int) = -(fx a - fx b) := by omega
  rw [e1, Int.natAbs_neg]

theorem epVictim_mirror (p : Pos) (m : Move) :
    epVictim (mirrorPos p) (mirrorMove m) = (epVictim p m).map fileMirror := by
  show (if ((mirrorPos p).board (mirrorMove m).src).any (·.kind == .pawn) &&
      (mirrorMove m).src.file != (mirrorMove m).dst.file &&
      empty (mirrorPos p).board (mirrorMove m).dst then
      some (sq (mirrorMove m).dst.file (mirrorMove m).src.rank) else none) =
    (if (p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file &&
      empty p.board m.dst then some (sq m.dst.file m.src.rank) else none).map fileMirror
  have hc1 : ((mirrorPos p).board (mirrorMove m).src).any (·.kind == .pawn) =
      (p.board m.src).any (·.kind == .pawn) := pawnAny_mirror p m
  have hc2 : ((mirrorMove m).src.file != (mirrorMove m).dst.file) = (m.src.file != m.dst.file) := by
    rw [show (mirrorMove m).src = fileMirror m.src from rfl,
      show (mirrorMove m).dst = fileMirror m.dst from rfl, file_fileMirror, file_fileMirror]
    have h1 : m.src.file < 8 := Nat.mod_lt _ (by decide)
    have h2 : m.dst.file < 8 := Nat.mod_lt _ (by decide)
    cases h : (m.src.file != m.dst.file)
    · rw [bne_eq_false_iff_eq] at h ⊢
      omega
    · rw [bne_iff_ne] at h ⊢
      intro hcontra
      apply h
      omega
  have hc3 : empty (mirrorPos p).board (mirrorMove m).dst = empty p.board m.dst := by
    show empty (mirrorPos p).board (fileMirror m.dst) = empty p.board m.dst
    exact empty_mirror p.board m.dst
  rw [hc1, hc2, hc3]
  rw [show (mirrorMove m).dst = fileMirror m.dst from rfl, file_fileMirror,
    show (mirrorMove m).src = fileMirror m.src from rfl, rank_fileMirror]
  by_cases hcond : ((p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file &&
      empty p.board m.dst) = true
  · rw [if_pos hcond, if_pos hcond, Option.map_some]
    apply congrArg some
    rw [sq_mirror m.dst.file m.src.rank (Nat.mod_lt _ (by decide)) (by
      have h1 := m.src.isLt
      show m.src.val / 8 < 8
      omega)]
  · rw [if_neg hcond, if_neg hcond, Option.map_none]

theorem isCapture_mirror (p : Pos) (m : Move) :
    isCapture (mirrorPos p) (mirrorMove m) = isCapture p m := by
  unfold isCapture
  have eb : ((mirrorPos p).board (mirrorMove m).dst).isSome = (p.board m.dst).isSome := by
    show (p.board (fileMirror (fileMirror m.dst))).isSome = _
    rw [fileMirror_invol]
  rw [eb, epVictim_mirror]
  cases epVictim p m <;> rfl

def movedPiece (p : Pos) (m : Move) : Option Piece :=
  match m.promo with
  | some k => (p.board m.src).map fun q => ⟨q.color, k⟩
  | none => p.board m.src

theorem movedPiece_mirror (p : Pos) (m : Move) :
    movedPiece (mirrorPos p) (mirrorMove m) = movedPiece p m := by
  have eB : (mirrorPos p).board (mirrorMove m).src = p.board m.src := by
    show p.board (fileMirror (fileMirror m.src)) = p.board m.src
    rw [fileMirror_invol]
  have eP : (mirrorMove m).promo = m.promo := rfl
  unfold movedPiece
  rw [eP, eB]

theorem play_board_norook (p : Pos) (m : Move) (hc : isCastle p m = false) (z : Sq) :
    (play p m).board z =
      (if z == m.dst then movedPiece p m
      else if z == m.src || epVictim p m == some z then none
      else p.board z) := by
  have h1 : ((p.board m.src).any (·.kind == .king) && m.src.file + 2 == m.dst.file) = false := by
    cases hf : (m.src.file + 2 == m.dst.file) <;> simp_all [isCastle, isKingMove]
  have h2 : ((p.board m.src).any (·.kind == .king) && m.dst.file + 2 == m.src.file) = false := by
    cases hf : (m.dst.file + 2 == m.src.file) <;> simp_all [isCastle, isKingMove]
  unfold play
  dsimp only
  simp only [h1, h2]
  rfl

theorem play_mirror (p : Pos) (m : Move) (hc : isCastle p m = false) :
    play (mirrorPos p) (mirrorMove m) = mirrorPos (play p m) := by
  have hc1 : isCastle (mirrorPos p) (mirrorMove m) = false := by rw [isCastle_mirror, hc]
  have h1 : (play (mirrorPos p) (mirrorMove m)).board = (mirrorPos (play p m)).board := by
    funext z
    have hR : (mirrorPos (play p m)).board z = (play p m).board (fileMirror z) := rfl
    rw [hR, play_board_norook p m hc (fileMirror z),
      play_board_norook (mirrorPos p) (mirrorMove m) hc1 z]
    have hMd : (mirrorMove m).dst = fileMirror m.dst := rfl
    have hMs : (mirrorMove m).src = fileMirror m.src := rfl
    rw [hMd, hMs]
    rw [beq_mirror', beq_mirror' z m.src, epVictim_mirror, beq_map_mirror, movedPiece_mirror]
    rfl
  have h2 : (play (mirrorPos p) (mirrorMove m)).turn = (mirrorPos (play p m)).turn := rfl
  have h3 : (play (mirrorPos p) (mirrorMove m)).castleK = (mirrorPos (play p m)).castleK := rfl
  have h4 : (play (mirrorPos p) (mirrorMove m)).castleQ = (mirrorPos (play p m)).castleQ := rfl
  have h5 : (play (mirrorPos p) (mirrorMove m)).ep = (mirrorPos (play p m)).ep := by
    show (if ((mirrorPos p).board (mirrorMove m).src).any (·.kind == .pawn) &&
        ((mirrorMove m).src.rank + 2 == (mirrorMove m).dst.rank ||
          (mirrorMove m).dst.rank + 2 == (mirrorMove m).src.rank) then
        some (sq (mirrorMove m).src.file (((mirrorMove m).src.rank + (mirrorMove m).dst.rank) / 2))
      else none) =
      (if (p.board m.src).any (·.kind == .pawn) &&
        (m.src.rank + 2 == m.dst.rank || m.dst.rank + 2 == m.src.rank) then
        some (sq m.src.file ((m.src.rank + m.dst.rank) / 2)) else none).map fileMirror
    rw [pawnAny_mirror]
    rw [show (mirrorMove m).src = fileMirror m.src from rfl,
      show (mirrorMove m).dst = fileMirror m.dst from rfl]
    rw [rank_fileMirror, rank_fileMirror, file_fileMirror]
    by_cases hcond : ((p.board m.src).any (·.kind == .pawn) &&
        (m.src.rank + 2 == m.dst.rank || m.dst.rank + 2 == m.src.rank)) = true
    · rw [if_pos hcond, if_pos hcond, Option.map_some]
      apply congrArg some
      rw [sq_mirror m.src.file ((m.src.rank + m.dst.rank) / 2) (Nat.mod_lt _ (by decide)) (by
        have h1 := m.src.isLt
        have h2 := m.dst.isLt
        show (m.src.val / 8 + m.dst.val / 8) / 2 < 8
        omega)]
    · rw [if_neg hcond, if_neg hcond, Option.map_none]
  have eL : play (mirrorPos p) (mirrorMove m) =
      ⟨(play (mirrorPos p) (mirrorMove m)).board, (play (mirrorPos p) (mirrorMove m)).turn,
        (play (mirrorPos p) (mirrorMove m)).castleK, (play (mirrorPos p) (mirrorMove m)).castleQ,
        (play (mirrorPos p) (mirrorMove m)).ep⟩ := rfl
  rw [eL, h1, h2, h3, h4, h5]

theorem legal_mirror (p : Pos) (m : Move) (hk : isKingMove p m = false) :
    mirrorMove m ∈ legalMoves (mirrorPos p) ↔ m ∈ legalMoves p := by
  unfold legalMoves
  rw [List.mem_filter, List.mem_filter]
  constructor
  · rintro ⟨hp, hs⟩
    constructor
    · unfold pseudo at hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · rw [List.mem_flatMap] at hp
        obtain ⟨s', -, hms'⟩ := hp
        cases hb : (mirrorPos p).board s' with
        | none =>
          rw [hb] at hms'
          exact absurd hms' (not_mem_nil' _)
        | some q =>
          rw [hb] at hms'
          dsimp only at hms'
          by_cases hcq : (q.color == p.turn) = true
          · rw [show (mirrorPos p).turn = p.turn from rfl, if_pos hcq] at hms'
            obtain ⟨hsrc, -, -⟩ := pieceMove_spec (mirrorPos p) s' q (mirrorMove m) hms'
            have hsrc' : fileMirror m.src = s' := hsrc
            subst hsrc'
            have e : (mirrorPos p).board (fileMirror m.src) = p.board m.src := by
              show p.board (fileMirror (fileMirror m.src)) = p.board m.src
              rw [fileMirror_invol]
            have hbq : p.board m.src = some q := e ▸ hb
            have hmp : m ∈ pieceMoves p m.src q := (pieceMoves_mirror p m.src q m).mp hms'
            unfold pseudo
            apply List.mem_append_left
            rw [List.mem_flatMap]
            refine ⟨m.src, mem_allSq _, ?_⟩
            rw [hbq]
            show m ∈ (if q.color == p.turn then pieceMoves p m.src q else [])
            rw [if_pos hcq]
            exact hmp
          · rw [show (mirrorPos p).turn = p.turn from rfl, if_neg hcq] at hms'
            exact absurd hms' (not_mem_nil' _)
      · exfalso
        obtain ⟨h1, h2, -, -⟩ := castleMove_spec (mirrorPos p) (mirrorMove m) hp
        have hk2 : (mirrorPos p).board (sq 4 (mirrorPos p).turn.home) =
            some ⟨(mirrorPos p).turn, .king⟩ := h1 ▸ h2
        have hkm : isKingMove (mirrorPos p) (mirrorMove m) = true :=
          kingMove_true_of_board (mirrorPos p) (mirrorPos p).turn (sq 4 (mirrorPos p).turn.home) hk2
            (mirrorMove m) h1
        rw [isKingMove_mirror, hk] at hkm
        exact Bool.noConfusion hkm
    · have hcc : isCastle p m = false := by
        show (isKingMove p m && _) = false
        rw [hk]
        rfl
      have h1e : inCheck (play p m) p.turn = inCheck (play (mirrorPos p) (mirrorMove m)) p.turn := by
        have e1 := inCheck_mirror (play p m) p.turn
        rw [← play_mirror p m hcc] at e1
        exact e1.symm
      rw [h1e]
      exact hs
  · rintro ⟨hp, hs⟩
    constructor
    · have hleg : m ∈ legalMoves p := List.mem_filter.mpr ⟨hp, hs⟩
      obtain ⟨q, hq, hcq, hmem⟩ := legal_nonking_mem p m hleg hk
      unfold pseudo
      apply List.mem_append_left
      rw [List.mem_flatMap]
      refine ⟨fileMirror m.src, mem_allSq _, ?_⟩
      have hbq : (mirrorPos p).board (fileMirror m.src) = some q := by
        show p.board (fileMirror (fileMirror m.src)) = some q
        rw [fileMirror_invol]
        exact hq
      rw [hbq]
      have hcond : (q.color == p.turn) = true := beq_iff_eq.mpr hcq
      show mirrorMove m ∈ (if q.color == (mirrorPos p).turn then
        pieceMoves (mirrorPos p) (fileMirror m.src) q else [])
      rw [show (mirrorPos p).turn = p.turn from rfl, if_pos hcond]
      exact (pieceMoves_mirror p m.src q m).mpr hmem
    · have hcc : isCastle p m = false := by
        show (isKingMove p m && _) = false
        rw [hk]
        rfl
      have hX : inCheck (play (mirrorPos p) (mirrorMove m)) (mirrorPos p).turn =
          inCheck (play p m) p.turn := by
        rw [play_mirror p m hcc]
        exact inCheck_mirror (play p m) p.turn
      rw [hX]
      exact hs

theorem givesCheck_mirror (p : Pos) (m : Move) (hc : isCastle p m = false) :
    givesCheck (mirrorPos p) (mirrorMove m) = givesCheck p m := by
  show inCheck (play (mirrorPos p) (mirrorMove m)) (mirrorPos p).turn.opp = inCheck (play p m) p.turn.opp
  rw [play_mirror p m hc]
  exact inCheck_mirror (play p m) p.turn.opp

theorem kf_mirror (p : Pos) (ms : List Move) (h : KFChain p ms) :
    KFChain (mirrorPos p) (ms.map mirrorMove) ∧ caps (mirrorPos p) (ms.map mirrorMove) = caps p ms := by
  revert h
  induction ms generalizing p with
  | nil => intro h; exact ⟨trivial, rfl⟩
  | cons m ms ih =>
    intro h
    obtain ⟨hl, hg, hk, hrest⟩ := h
    have hcc : isCastle p m = false := by
      show (isKingMove p m && _) = false
      rw [hk]
      rfl
    have hkm : isKingMove (mirrorPos p) (mirrorMove m) = false := by rw [isKingMove_mirror]; exact hk
    obtain ⟨ih1, ih2⟩ := ih (play p m) hrest
    constructor
    · show mirrorMove m ∈ legalMoves (mirrorPos p) ∧ givesCheck (mirrorPos p) (mirrorMove m) = true ∧
        isKingMove (mirrorPos p) (mirrorMove m) = false ∧ _
      refine ⟨(legal_mirror p m hk).mpr hl, ?_, hkm, ?_⟩
      · rw [givesCheck_mirror p m hcc]
        exact hg
      · rw [play_mirror p m hcc]
        exact ih1
    · show (if isCapture (mirrorPos p) (mirrorMove m) then 1 else 0) +
          caps (play (mirrorPos p) (mirrorMove m)) (ms.map mirrorMove) =
        (if isCapture p m then 1 else 0) + caps (play p m) ms
      rw [play_mirror p m hcc, ih2, isCapture_mirror]

theorem c0_mirror (p : Pos) (h : C0 p) : C0 (mirrorPos p) := by
  obtain ⟨wk, bk, apart, pawns, safe, epf⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := wk
    refine ⟨fileMirror w, fun s => ?_⟩
    constructor
    · intro hs
      have e : p.board (fileMirror s) = some ⟨.white, .king⟩ := hs
      have h1 : fileMirror s = w := (hw (fileMirror s)).mp e
      have h2 := congrArg fileMirror h1
      rw [fileMirror_invol] at h2
      exact h2
    · intro hs
      rw [hs]
      show p.board (fileMirror (fileMirror w)) = some ⟨.white, .king⟩
      rw [fileMirror_invol]
      exact (hw w).mpr rfl
  · obtain ⟨w, hw⟩ := bk
    refine ⟨fileMirror w, fun s => ?_⟩
    constructor
    · intro hs
      have e : p.board (fileMirror s) = some ⟨.black, .king⟩ := hs
      have h1 : fileMirror s = w := (hw (fileMirror s)).mp e
      have h2 := congrArg fileMirror h1
      rw [fileMirror_invol] at h2
      exact h2
    · intro hs
      rw [hs]
      show p.board (fileMirror (fileMirror w)) = some ⟨.black, .king⟩
      rw [fileMirror_invol]
      exact (hw w).mpr rfl
  · intro w' b' hw' hb'
    have e1 : p.board (fileMirror w') = some ⟨.white, .king⟩ := hw'
    have e2 : p.board (fileMirror b') = some ⟨.black, .king⟩ := hb'
    have h3 := apart (fileMirror w') (fileMirror b') e1 e2
    rw [kdist_mirror] at h3
    exact h3
  · intro s c hs
    have e : p.board (fileMirror s) = some ⟨c, .pawn⟩ := hs
    obtain ⟨h1, h2⟩ := pawns (fileMirror s) c e
    have hry : ry (fileMirror s) = ry s := (fileMirror_coords s).2
    rw [hry] at h1 h2
    exact ⟨h1, h2⟩
  · show inCheck (mirrorPos p) p.turn.opp = false
    rw [inCheck_mirror]
    exact safe
  · intro t ht
    obtain ⟨u, hu, htu⟩ := Option.map_eq_some_iff.mp ht
    obtain ⟨hry, hem, ⟨o1, ho1, hbo1⟩, ⟨d1, hd1, hbd1⟩⟩ := epf u hu
    subst htu
    refine ⟨?_, ?_, ?_, ?_⟩
    · show ry (fileMirror u) = _
      rw [(fileMirror_coords u).2]
      exact hry
    · show p.board (fileMirror (fileMirror u)) = none
      rw [fileMirror_invol]
      exact hem
    · refine ⟨fileMirror o1, ?_, ?_⟩
      · show off (fileMirror u) 0 p.turn.fwd = some (fileMirror o1)
        rw [show off (fileMirror u) 0 p.turn.fwd = (off u 0 p.turn.fwd).map fileMirror from
          off_mirror u 0 p.turn.fwd]
        rw [ho1]
        rfl
      · show p.board (fileMirror (fileMirror o1)) = none
        rw [fileMirror_invol]
        exact hbo1
    · refine ⟨fileMirror d1, ?_, ?_⟩
      · show off (fileMirror u) 0 (-p.turn.fwd) = some (fileMirror d1)
        rw [show off (fileMirror u) 0 (-p.turn.fwd) = (off u 0 (-p.turn.fwd)).map fileMirror from
          off_mirror u 0 (-p.turn.fwd)]
        rw [hd1]
        rfl
      · show p.board (fileMirror (fileMirror d1)) = some ⟨p.turn.opp, .pawn⟩
        rw [fileMirror_invol]
        exact hbd1

theorem flipSq_eq_rankMirror (s : Sq) : All63.flipSq s = rankMirror s := by
  have h : ∀ v, v < 64 → v ^^^ 56 = (7 - v / 8) * 8 + v % 8 := by decide
  apply Fin.ext
  show s.val ^^^ 56 = (7 - s.val / 8) * 8 + s.val % 8
  exact h s.val s.isLt

theorem flipSq_fun : All63.flipSq = rankMirror := funext flipSq_eq_rankMirror

theorem swap_board (p : Pos) (s : Sq) : (swapPos p).board s = (p.board (rankMirror s)).map swapPiece := rfl

theorem swapMove_src (m : Move) : (swapMove m).src = rankMirror m.src := rfl

theorem swapMove_dst (m : Move) : (swapMove m).dst = rankMirror m.dst := rfl

theorem swap_turn (p : Pos) : (swapPos p).turn = p.turn.opp := rfl

theorem opp_fwd (c : Color) : c.opp.fwd = -c.fwd := by cases c <;> rfl

theorem neg_opp_fwd (c : Color) : -(c.opp.fwd) = c.fwd := by cases c <;> rfl

theorem swapPiece_invol (q : Piece) : swapPiece (swapPiece q) = q := by
  cases q with | mk c k => cases c <;> rfl

theorem swapPiece_fl (q : Piece) : swapPiece q = All63.flipPiece q := rfl

theorem swapPiece_opp (c : Color) (k : Kind) : swapPiece ⟨c.opp, k⟩ = ⟨c, k⟩ := by cases c <;> rfl

theorem any_kind_swap (o : Option Piece) (k : Kind) :
    ((o.map swapPiece).any fun q => q.kind == k) = (o.any fun q => q.kind == k) := by
  cases o with | none => rfl | some q => rfl

theorem any_kind_flip (o : Option Piece) (k : Kind) :
    ((o.map All63.flipPiece).any fun q => q.kind == k) = (o.any fun q => q.kind == k) := by
  cases o with | none => rfl | some q => rfl

theorem flip_board (p : Pos) (s : Sq) :
    (All63.flipPos p).board s = (p.board (All63.flipSq s)).map All63.flipPiece := rfl

theorem flipMove_src (m : Move) : (All63.flipMove m).src = All63.flipSq m.src := rfl

theorem swapBoard_eq (b : Board) : (fun z => (b (rankMirror z)).map swapPiece) = All63.flipBoard b := by
  rw [← flipSq_fun]
  funext z
  show (b (All63.flipSq z)).map swapPiece = (b (All63.flipSq z)).map All63.flipPiece
  cases b (All63.flipSq z) with
  | none => rfl
  | some q => rfl

theorem rankMirror_file (s : Sq) : (rankMirror s).file = s.file :=
  Int.ofNat_inj.mp (rankMirror_coords s).1

theorem kdist_swap (a b : Sq) : kdist (rankMirror a) (rankMirror b) = kdist a b := by
  obtain ⟨h1, h2⟩ := rankMirror_coords a
  obtain ⟨h3, h4⟩ := rankMirror_coords b
  simp only [kdist]
  rw [h1, h2, h3, h4]
  have e : ((7 : Int) - ry a - (7 - ry b)).natAbs = (ry a - ry b).natAbs := by omega
  rw [e]

theorem off_swap (s : Sq) (df dr : Int) : off (rankMirror s) df (-dr) = (off s df dr).map rankMirror := by
  have h := All63.off_flip s df dr
  rwa [flipSq_fun] at h

theorem off_swap' (s : Sq) (df dr : Int) : off (rankMirror s) df dr = (off s df (-dr)).map rankMirror := by
  have h := off_swap s df (-dr)
  rwa [Int.neg_neg] at h

theorem swapMove_eq (m : Move) : swapMove m = All63.flipMove m := by
  cases m with | mk s d pr =>
  show (⟨rankMirror s, rankMirror d, pr⟩ : Move) = ⟨All63.flipSq s, All63.flipSq d, pr⟩
  rw [flipSq_eq_rankMirror, flipSq_eq_rankMirror]

theorem swapPos_eq (p : Pos) : swapPos p = noCastle (All63.flipPos p) := by
  obtain ⟨b, t, cK, cQ, e⟩ := p
  have hL : swapPos ⟨b, t, cK, cQ, e⟩ = Pos.mk (fun s => (b (rankMirror s)).map swapPiece) t.opp
      (fun _ => false) (fun _ => false) (e.map rankMirror) := rfl
  have hR : noCastle (All63.flipPos ⟨b, t, cK, cQ, e⟩) =
      Pos.mk (fun s => (b (All63.flipSq s)).map All63.flipPiece) t.opp
        (fun _ => false) (fun _ => false) (e.map All63.flipSq) := rfl
  rw [hL, hR, Pos.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, ?_⟩
  · funext s
    show (b (rankMirror s)).map swapPiece = (b (All63.flipSq s)).map All63.flipPiece
    rw [flipSq_eq_rankMirror]
    cases b (All63.flipSq s) with
    | none => rfl
    | some q => rfl
  · show e.map rankMirror = e.map All63.flipSq
    rw [flipSq_fun]

theorem inCheck_noCastle (p : Pos) (c : Color) : inCheck (noCastle p) c = inCheck p c := rfl

theorem isKingMove_swap (p : Pos) (m : Move) : isKingMove (swapPos p) (swapMove m) = isKingMove p m := by
  unfold isKingMove
  rw [swapMove_src, swap_board, rankMirror_invol, any_kind_swap]

theorem isCapture_swap (p : Pos) (m : Move) : isCapture (swapPos p) (swapMove m) = isCapture p m := by
  have h1 : ((swapPos p).board (swapMove m).dst).isSome = (p.board m.dst).isSome := by
    rw [swapMove_dst, swap_board, rankMirror_invol]
    cases p.board m.dst <;> rfl
  have h2 : (epVictim (swapPos p) (swapMove m)).isSome = (epVictim p m).isSome := by
    have hp : ((swapPos p).board (swapMove m).src).any (fun q => q.kind == Kind.pawn) =
        (p.board m.src).any (fun q => q.kind == Kind.pawn) := by
      rw [swapMove_src, swap_board, rankMirror_invol, any_kind_swap]
    have hf : ((swapMove m).src.file != (swapMove m).dst.file) = (m.src.file != m.dst.file) := by
      rw [swapMove_src, swapMove_dst, rankMirror_file, rankMirror_file]
    have he : empty (swapPos p).board (swapMove m).dst = empty p.board m.dst := by
      show ((p.board (rankMirror (rankMirror m.dst))).map swapPiece).isNone = (p.board m.dst).isNone
      rw [rankMirror_invol]
      cases p.board m.dst <;> rfl
    unfold epVictim
    rw [hp, hf, he]
    by_cases hC :
      ((p.board m.src).any (fun q => q.kind == Kind.pawn) && m.src.file != m.dst.file &&
        empty p.board m.dst) = true
    · rw [if_pos hC, if_pos hC]
      rfl
    · rw [if_neg hC, if_neg hC]
  unfold isCapture
  rw [h1, h2]

theorem attacks_swap (b : Board) (s t : Sq) (q : Piece) :
    rankMirror t ∈ attacks (fun z => (b (rankMirror z)).map swapPiece) (rankMirror s) (swapPiece q) ↔
      t ∈ attacks b s q := by
  rw [swapBoard_eq, ← flipSq_eq_rankMirror s, ← flipSq_eq_rankMirror t, swapPiece_fl]
  exact All63.mem_attacks_flip b s t q

theorem inCheck_swap (p : Pos) (c : Color) : inCheck (swapPos p) c.opp = inCheck p c := by
  rw [swapPos_eq p, inCheck_noCastle]
  exact All63.inCheck_flip p c

theorem play_swap (p : Pos) (m : Move) (_ : isCastle p m = false) :
    play (swapPos p) (swapMove m) = swapPos (play p m) := by
  rw [swapPos_eq p, swapMove_eq m, play_noCastle, All63.play_flip, swapPos_eq]

theorem legal_swap (p : Pos) (m : Move) (hk : isKingMove p m = false) :
    swapMove m ∈ legalMoves (swapPos p) ↔ m ∈ legalMoves p := by
  rw [swapPos_eq p, swapMove_eq m]
  have e : isKingMove (All63.flipPos p) (All63.flipMove m) = isKingMove p m := by
    unfold isKingMove
    rw [flipMove_src, flip_board, All63.flipSq_flipSq, any_kind_flip]
  have hkf : isKingMove (All63.flipPos p) (All63.flipMove m) = false := by rw [e]; exact hk
  rw [show noCastle (All63.flipPos p) =
    { All63.flipPos p with castleK := fun _ => false, castleQ := fun _ => false } from rfl]
  rw [← legal_castleRights_indep (All63.flipPos p) (All63.flipMove m) hkf]
  exact All63.mem_legal_flip p m

theorem givesCheck_swap (p : Pos) (m : Move) (hc : isCastle p m = false) :
    givesCheck (swapPos p) (swapMove m) = givesCheck p m := by
  show inCheck (play (swapPos p) (swapMove m)) (swapPos p).turn.opp = inCheck (play p m) p.turn.opp
  rw [play_swap p m hc, inCheck_swap (play p m) (swapPos p).turn]
  rfl

theorem kf_swap (p : Pos) (ms : List Move) (h : KFChain p ms) :
    KFChain (swapPos p) (ms.map swapMove) ∧ caps (swapPos p) (ms.map swapMove) = caps p ms := by
  induction ms generalizing p with
  | nil => exact ⟨trivial, rfl⟩
  | cons m ms ih =>
    obtain ⟨hm1, hm2, hm3, hm4⟩ := h
    have hc : isCastle p m = false := by simp only [isCastle, hm3, Bool.false_and]
    obtain ⟨ih1, ih2⟩ := ih (play p m) hm4
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact (legal_swap p m hm3).mpr hm1
    · rw [givesCheck_swap p m hc]; exact hm2
    · rw [isKingMove_swap]; exact hm3
    · rw [play_swap p m hc]; exact ih1
    · show (if isCapture (swapPos p) (swapMove m) then 1 else 0) +
          caps (play (swapPos p) (swapMove m)) (List.map swapMove ms) =
        (if isCapture p m then 1 else 0) + caps (play p m) ms
      rw [isCapture_swap, play_swap p m hc, ih2]

theorem board_swap (p : Pos) (s : Sq) (q : Piece) :
    (swapPos p).board s = some q ↔ p.board (rankMirror s) = some (swapPiece q) := by
  show (p.board (rankMirror s)).map swapPiece = some q ↔ p.board (rankMirror s) = some (swapPiece q)
  cases h : p.board (rankMirror s) with
  | none => simp
  | some r =>
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro h2; rw [← h2, swapPiece_invol]
    · intro h2; rw [h2, swapPiece_invol]

theorem c0_swap (p : Pos) (h : C0 p) : C0 (swapPos p) := by
  obtain ⟨hwk, hbk, hapart, hpawns, hsafe, hep⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hbk
    refine ⟨rankMirror b, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · have hbs : p.board (rankMirror s) = some ⟨.black, .king⟩ := (board_swap p s ⟨.white, .king⟩).mp hs
      have hrb : rankMirror s = b := (hb _).mp hbs
      have h2 := congrArg rankMirror hrb
      rwa [rankMirror_invol] at h2
    · rw [hs]
      show (p.board (rankMirror (rankMirror b))).map swapPiece = some ⟨.white, .king⟩
      rw [rankMirror_invol, (hb b).mpr rfl]
      rfl
  · obtain ⟨w, hw⟩ := hwk
    refine ⟨rankMirror w, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · have hbs : p.board (rankMirror s) = some ⟨.white, .king⟩ := (board_swap p s ⟨.black, .king⟩).mp hs
      have hrw : rankMirror s = w := (hw _).mp hbs
      have h2 := congrArg rankMirror hrw
      rwa [rankMirror_invol] at h2
    · rw [hs]
      show (p.board (rankMirror (rankMirror w))).map swapPiece = some ⟨.black, .king⟩
      rw [rankMirror_invol, (hw w).mpr rfl]
      rfl
  · intro w' b' hw' hb'
    have h2 : p.board (rankMirror b') = some ⟨.white, .king⟩ := (board_swap _ _ _).mp hb'
    have h1 : p.board (rankMirror w') = some ⟨.black, .king⟩ := (board_swap _ _ _).mp hw'
    have h3 := hapart _ _ h2 h1
    rw [kdist_swap, kdist_comm] at h3
    exact h3
  · intro s c hs
    have hbs : p.board (rankMirror s) = some ⟨c.opp, .pawn⟩ := (board_swap _ _ _).mp hs
    obtain ⟨h1, h2⟩ := hpawns _ _ hbs
    obtain ⟨-, h4⟩ := rankMirror_coords s
    rw [h4] at h1 h2
    exact ⟨by omega, by omega⟩
  · have h2 := inCheck_swap p (swapPos p).turn
    rw [h2]; exact hsafe
  · intro t' ht'
    have ht2 : p.ep.map rankMirror = some t' := ht'
    cases hE : p.ep with
    | none => rw [hE] at ht2; simp at ht2
    | some t =>
      rw [hE, Option.map_some, Option.some.injEq] at ht2
      subst ht2
      obtain ⟨hr, hb, ho, hd⟩ := hep t hE
      obtain ⟨o, hoo, hbo⟩ := ho
      obtain ⟨d, hdd, hbd⟩ := hd
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [(rankMirror_coords t).2]
        show (7 : Int) - ry t = (if p.turn.opp = .white then 5 else 2)
        cases htn : p.turn with
        | white =>
          rw [htn] at hr
          have hr5 : ry t = (5 : Int) := hr
          rw [hr5]
          decide
        | black =>
          rw [htn] at hr
          have hr2 : ry t = (2 : Int) := hr
          rw [hr2]
          decide
      · show (p.board (rankMirror (rankMirror t))).map swapPiece = none
        rw [rankMirror_invol, hb]
        rfl
      · refine ⟨rankMirror o, ?_, ?_⟩
        · show off (rankMirror t) 0 (p.turn.opp.fwd) = some (rankMirror o)
          rw [opp_fwd, off_swap, hoo]
          rfl
        · show (p.board (rankMirror (rankMirror o))).map swapPiece = none
          rw [rankMirror_invol, hbo]
          rfl
      · refine ⟨rankMirror d, ?_, ?_⟩
        · show off (rankMirror t) 0 (-(p.turn.opp.fwd)) = some (rankMirror d)
          rw [neg_opp_fwd, off_swap', hdd]
          rfl
        · show (p.board (rankMirror (rankMirror d))).map swapPiece = some ⟨(swapPos p).turn.opp, .pawn⟩
          rw [rankMirror_invol, hbd]
          show some (swapPiece ⟨p.turn.opp, .pawn⟩) = some ⟨(swapPos p).turn.opp, .pawn⟩
          rw [swapPiece_opp]
          show (some ⟨p.turn, .pawn⟩ : Option Piece) = some ⟨p.turn.opp.opp, .pawn⟩
          rw [Color.opp_opp]

def lexLe (a b : Sq × Sq) : Bool := a.1.val < b.1.val || (a.1.val == b.1.val && a.2.val ≤ b.2.val)

def reps : List (Sq × Sq) :=
  (allSq.flatMap fun w => allSq.map fun b => (w, b)).filter fun wb =>
    2 ≤ kdist wb.1 wb.2 && lexLe wb (fileMirror wb.1, fileMirror wb.2)

set_option maxRecDepth 100000 in
theorem reps_length : reps.length = 1806 := by decide +kernel

theorem kdist_fileMirror (a b : Sq) : kdist (fileMirror a) (fileMirror b) = kdist a b := by
  obtain ⟨h1, h2⟩ := fileMirror_coords a
  obtain ⟨h3, h4⟩ := fileMirror_coords b
  simp only [kdist]
  rw [h1, h2, h3, h4]
  have e : ((7 : Int) - fx a - (7 - fx b)).natAbs = (fx a - fx b).natAbs := by omega
  rw [e]

theorem lexLe_total (a b : Sq × Sq) : lexLe a b = true ∨ lexLe b a = true := by
  rcases Nat.lt_trichotomy a.1.val b.1.val with h1 | h1 | h1
  · exact Or.inl (by simp [lexLe, h1])
  · rcases Nat.le_total a.2.val b.2.val with h2 | h2
    · exact Or.inl (by simp [lexLe, h1, h2])
    · exact Or.inr (by simp [lexLe, h1, h2])
  · exact Or.inr (by simp [lexLe, h1])

theorem mem_reps (w b : Sq) : (w, b) ∈ reps ↔ 2 ≤ kdist w b ∧ lexLe (w, b) (fileMirror w, fileMirror b) = true := by
  unfold reps
  rw [List.mem_filter]
  constructor
  · intro hmem
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hmem.2
    exact ⟨of_decide_eq_true h1, h2⟩
  · intro hcd
    exact ⟨List.mem_flatMap.mpr ⟨w, mem_allSq w, List.mem_map.mpr ⟨b, mem_allSq b, rfl⟩⟩,
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true hcd.1, hcd.2⟩⟩

theorem reps_cover (w b : Sq) (h : 2 ≤ kdist w b) : (w, b) ∈ reps ∨ (fileMirror w, fileMirror b) ∈ reps := by
  rcases lexLe_total (w, b) (fileMirror w, fileMirror b) with h1 | h1
  · exact Or.inl ((mem_reps w b).mpr ⟨h, h1⟩)
  · refine Or.inr ((mem_reps _ _).mpr ⟨?_, ?_⟩)
    · rw [kdist_fileMirror]
      exact h
    · rw [fileMirror_invol w, fileMirror_invol b]
      exact h1

theorem c0_kings (p : Pos) (h : C0 p) : ∃ w b, kingAt p .white w ∧ kingAt p .black b ∧ 2 ≤ kdist w b := by
  obtain ⟨w, hw⟩ := h.wk
  obtain ⟨b, hb⟩ := h.bk
  have hkw : kingAt p .white w := (hw w).mpr rfl
  have hkb : kingAt p .black b := (hb b).mpr rfl
  exact ⟨w, b, hkw, hkb, h.apart w b hkw hkb⟩

theorem noChain_white (n m : Nat) (h : ∀ wb ∈ reps, NoChain wb.1 wb.2 n m) (p : Pos) (ms : List Move)
    (hc : C0 p) (ht : p.turn = .white) (hk : KFChain p ms) (hn : ms.length = n) (hm : caps p ms ≤ m) : False := by
  obtain ⟨w, b, hkw, hkb, hd⟩ := c0_kings p hc
  rcases reps_cover w b hd with hr | hr
  · exact h (w, b) hr p ms ⟨hc, ht, hkw, hkb, hk, hn, hm⟩
  · obtain ⟨hk2, hcap2⟩ := kf_mirror p ms hk
    have hkc : C0 (mirrorPos p) := c0_mirror p hc
    have htw : (mirrorPos p).turn = .white := ht
    have hkw2 : kingAt (mirrorPos p) .white (fileMirror w) := by
      show p.board (fileMirror (fileMirror w)) = some ⟨.white, .king⟩
      rw [fileMirror_invol]
      exact hkw
    have hkb2 : kingAt (mirrorPos p) .black (fileMirror b) := by
      show p.board (fileMirror (fileMirror b)) = some ⟨.black, .king⟩
      rw [fileMirror_invol]
      exact hkb
    have hlen2 : (ms.map mirrorMove).length = n := by rw [List.length_map]; exact hn
    have hcap2' : caps (mirrorPos p) (ms.map mirrorMove) ≤ m := by rw [hcap2]; exact hm
    exact h (fileMirror w, fileMirror b) hr (mirrorPos p) (ms.map mirrorMove)
      ⟨hkc, htw, hkw2, hkb2, hk2, hlen2, hcap2'⟩

theorem noChain_any (n m : Nat) (h : ∀ wb ∈ reps, NoChain wb.1 wb.2 n m) (p : Pos) (ms : List Move)
    (hc : C0 p) (hk : KFChain p ms) (hn : ms.length = n) (hm : caps p ms ≤ m) : False := by
  cases ht : p.turn with
  | white => exact noChain_white n m h p ms hc ht hk hn hm
  | black =>
    obtain ⟨hk2, hcap2⟩ := kf_swap p ms hk
    have hcs : C0 (swapPos p) := c0_swap p hc
    have hts : (swapPos p).turn = .white := by
      show p.turn.opp = .white
      rw [ht]
      rfl
    have hlen2 : (ms.map swapMove).length = n := by rw [List.length_map]; exact hn
    have hcap2' : caps (swapPos p) (ms.map swapMove) ≤ m := by rw [hcap2]; exact hm
    exact noChain_white n m h (swapPos p) (ms.map swapMove) hcs hts hk2 hlen2 hcap2'

theorem noChain_mono (w b : Sq) (n n' m : Nat) (h : NoChain w b n m) (hn : n ≤ n') : NoChain w b n' m := by
  intro p ms ⟨hc, ht, hw, hb, hk, hl, hm⟩
  have ⟨hk', hcap⟩ := kf_take p ms n hk
  exact h p (ms.take n) ⟨hc, ht, hw, hb, hk', by simp [hl]; omega, by omega⟩

theorem boundB_of_noChain (k L : Nat) (h : ∀ wb ∈ reps, NoChain wb.1 wb.2 (L + 1) k) : BoundB k L := by
  intro p ms hc hk hcap
  refine Nat.le_of_not_lt fun hlen => ?_
  have ⟨hk', hcap'⟩ := kf_take p ms (L + 1) hk
  exact noChain_any (L + 1) k h p (ms.take (L + 1)) hc hk' (by simp; omega) (by omega)

end Chess.C364
