import ChessProof.All63.Frame
import ChessProof.All63.Invariant
import ChessProof.All63.Symmetry
import ChessProof.All63.Cases

namespace Chess.All63

def CfgOk (c : Cfg) : Prop := c.kw < 64 ∧ c.kb < 64 ∧ 1 < cheb c.kw c.kb

def Layout (c : Cfg) (s : St) : Prop :=
  ∀ q ∈ c.squares, ∀ k < 11, 0 < c.xv q k ∧ s.defs[(c.xv q k).toNat - 1]? = some (.x q k)

def RightsOk (c : Cfg) (s : St) (r : Rights) : Prop :=
  (∀ f v, (f, v) ∈ r.ep → f < 8 ∧ 0 < v ∧ s.defs[v.toNat - 1]? = some (.ep f)) ∧
  (∀ f < 8, (r.ep.lookup f).isSome = !(c.isK (f + 32) || c.isK (f + 40) || c.isK (f + 48))) ∧
  (∀ b v, (b, v) ∈ r.cr → 0 < v ∧ s.defs[v.toNat - 1]? = some (.cr b)) ∧
  (∀ b, (r.cr.lookup b).isSome = (c.kw == E1 && !c.chk && (if b then H1 else A1) != c.kb))

def Agrees (p : Pos) (b' : Board) (emp occ excl : List Nat) : Prop :=
  (∀ q < 64, q ∉ emp → q ∉ occ → q ∉ excl → b' (toSq q) = p.board (toSq q)) ∧
  (∀ q ∈ emp, q ∉ occ → b' (toSq q) = none) ∧ (∀ q ∈ occ, b' (toSq q) ≠ none)

def colOf (white : Bool) : Color := if white then .white else .black

def NonGateSat (A : Assignment) (s s' : St) : Prop := ∀ fc ∈ NewCls s s', fc.1 ≠ .gate → fc.2.sat A = true

theorem cheb_toSq_tab : ∀ a ∈ List.range 64, ∀ b ∈ List.range 64,
    cheb a b = dist (toSq a) (toSq b) := by
  decide +kernel

theorem cheb_toSq (a b : Nat) (ha : a < 64) (hb : b < 64) : cheb a b = dist (toSq a) (toSq b) :=
  cheb_toSq_tab a (List.mem_range.mpr ha) b (List.mem_range.mpr hb)

theorem toSq_val (s : Sq) : toSq s.val = s :=
  Fin.ext (by simp [toSq, Nat.mod_eq_of_lt s.isLt])

theorem toSq_val_of_lt (q : Nat) (h : q < 64) : (toSq q).val = q := by
  simp [toSq, Nat.mod_eq_of_lt h]

theorem fits_cfgOk {c : Cfg} {p : Pos} (hf : Fits c p) : CfgOk c := by
  obtain ⟨hA, -, hc⟩ := hf
  subst hc
  refine ⟨Fin.is_lt _, Fin.is_lt _, ?_⟩
  show 1 < cheb (kingSq p .white).val (kingSq p .black).val
  rw [cheb_toSq _ _ (Fin.is_lt _) (Fin.is_lt _), toSq_val, toSq_val]
  exact hA.apart

theorem fits_kings {c : Cfg} {p : Pos} (hf : Fits c p) :
    p.board (toSq c.kw) = some ⟨.white, .king⟩ ∧ p.board (toSq c.kb) = some ⟨.black, .king⟩ ∧
    ∀ q < 64, q ≠ c.kw → q ≠ c.kb → symOf (p.board (toSq q)) < 11 := by
  obtain ⟨hA, -, hc⟩ := hf
  subst hc
  obtain ⟨hw, hwu⟩ := kingSq_spec p .white (hA.kings .white)
  obtain ⟨hb, hbu⟩ := kingSq_spec p .black (hA.kings .black)
  refine ⟨?_, ?_, ?_⟩
  · show p.board (toSq (kingSq p .white).val) = _
    rw [toSq_val]
    exact hw
  · show p.board (toSq (kingSq p .black).val) = _
    rw [toSq_val]
    exact hb
  · intro q hq hqw hqk
    match h : p.board (toSq q) with
    | none => decide
    | some ⟨.white, .king⟩ =>
      exact absurd
        (show q = (kingSq p .white).val by rw [← toSq_val_of_lt q hq, hwu (toSq q) h]) hqw
    | some ⟨.black, .king⟩ =>
      exact absurd
        (show q = (kingSq p .black).val by rw [← toSq_val_of_lt q hq, hbu (toSq q) h]) hqk
    | some ⟨.white, .pawn⟩ => decide
    | some ⟨.white, .knight⟩ => decide
    | some ⟨.white, .bishop⟩ => decide
    | some ⟨.white, .rook⟩ => decide
    | some ⟨.white, .queen⟩ => decide
    | some ⟨.black, .pawn⟩ => decide
    | some ⟨.black, .knight⟩ => decide
    | some ⟨.black, .bishop⟩ => decide
    | some ⟨.black, .rook⟩ => decide
    | some ⟨.black, .queen⟩ => decide


theorem rayL_tab : ∀ s ∈ List.range 64, ∀ t ∈ List.range 64, ∀ d ∈ orth ++ diag,
    (t ∈ rayL s d ↔ direction s t = some d) := by
  decide +kernel

theorem mem_rayL_iff (s t : Nat) (hs : s < 64) (ht : t < 64) (d : Int × Int) (hd : d ∈ orth ++ diag) :
    t ∈ rayL s d ↔ direction s t = some d :=
  rayL_tab s (List.mem_range.mpr hs) t (List.mem_range.mpr ht) d hd

theorem sqo_lt64 {f r : Int} {x : Nat} (h : sqo f r = some x) : x < 64 := by
  unfold sqo at h
  split at h
  · rename_i hb
    simp only [Option.some.injEq] at h
    have h2 : ((f + 8 * r).toNat : Int) = f + 8 * r := Int.toNat_of_nonneg (by omega)
    omega
  · simp at h

theorem rayGo_lt64 {d : Int × Int} : ∀ {n : Nat} {s x : Nat}, x ∈ rayGo d n s → x < 64 := by
  intro n
  induction n with
  | zero => intro s x h; simp [rayGo] at h
  | succ n ih =>
    intro s x h
    rw [rayGo] at h
    split at h
    · simp at h
    · next y hy =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact sqo_lt64 hy
      · exact ih h

theorem rayL_lt64 {s x : Nat} {d : Int × Int} (h : x ∈ rayL s d) : x < 64 := rayGo_lt64 h

theorem between_lt64 {a b u : Nat} (h : u ∈ between a b) : u < 64 := by
  unfold between at h
  split at h
  · simp at h
  · next d hd =>
    dsimp only at h
    split at h
    · exact rayL_lt64 (List.takeWhile_subset _ h)
    · simp at h

theorem between_tab : ∀ a ∈ List.range 64, ∀ b ∈ List.range 64, ∀ u ∈ List.range 64,
    (u ∈ between a b ↔ ∃ d, direction a b = some d ∧ u ∈ rayL a d ∧ b ∈ rayL u d) := by
  decide +kernel

theorem mem_between_iff (a b u : Nat) (ha : a < 64) (hb : b < 64) :
    u ∈ between a b ↔ ∃ d, direction a b = some d ∧ u ∈ rayL a d ∧ b ∈ rayL u d := by
  by_cases hu : u < 64
  · exact between_tab a (List.mem_range.mpr ha) b (List.mem_range.mpr hb) u (List.mem_range.mpr hu)
  · constructor
    · intro h
      exact absurd (between_lt64 h) hu
    · rintro ⟨d, -, h1, -⟩
      exact absurd (rayL_lt64 h1) hu

theorem between_rev_tab : ∀ a ∈ List.range 64, ∀ b ∈ List.range 64,
    between a b = (between b a).reverse := by
  decide +kernel

theorem between_symm (a b : Nat) (ha : a < 64) (hb : b < 64) : ∀ u, u ∈ between a b ↔ u ∈ between b a := by
  intro u
  rw [between_rev_tab a (List.mem_range.mpr ha) b (List.mem_range.mpr hb), List.mem_reverse]

theorem knightL_tab : ∀ a ∈ List.range 64, ∀ b ∈ List.range 64, (a ∈ knightL b ↔ b ∈ knightL a) := by
  decide +kernel

theorem mem_knightL_symm (a b : Nat) (ha : a < 64) (hb : b < 64) : a ∈ knightL b ↔ b ∈ knightL a :=
  knightL_tab a (List.mem_range.mpr ha) b (List.mem_range.mpr hb)

theorem off_eq_some (s t : Sq) (df dr : Int) :
    off s df dr = some t ↔ (t.file : Int) = s.file + df ∧ (t.rank : Int) = s.rank + dr := by
  have hsf : s.file < 8 := Nat.mod_lt _ (by decide)
  have hsr : s.rank < 8 := by have h := s.isLt; show s.val / 8 < 8; omega
  have htf : t.file < 8 := Nat.mod_lt _ (by decide)
  have htr : t.rank < 8 := by have h := t.isLt; show t.val / 8 < 8; omega
  have esf : (s.file : Int) = (s.val % 8 : Nat) := rfl
  have esr : (s.rank : Int) = (s.val / 8 : Nat) := rfl
  have etf : (t.file : Int) = (t.val % 8 : Nat) := rfl
  have etr : (t.rank : Int) = (t.val / 8 : Nat) := rfl
  constructor
  · intro h
    simp only [off, mkSq] at h
    split at h
    · next c1 =>
      split at h
      · next c2 =>
        have hv : t.val = ((s.rank : Int) + dr).toNat * 8 + ((s.file : Int) + df).toNat := by
          have h2 := congrArg Fin.val (Option.some.inj h)
          simpa using h2.symm
        constructor
        · rw [etf]
          have efm : t.val % 8 = ((s.file : Int) + df).toNat := by omega
          rw [efm, Int.toNat_of_nonneg c1.1, esf]
        · rw [etr]
          have erm : t.val / 8 = ((s.rank : Int) + dr).toNat := by omega
          rw [erm, Int.toNat_of_nonneg c1.2, esr]
      · simp at h
    · simp at h
  · rintro ⟨hf, hr⟩
    simp only [off, mkSq]
    have c1 : 0 ≤ (s.file : Int) + df ∧ 0 ≤ (s.rank : Int) + dr := by omega
    rw [if_pos c1]
    have c2 : ((s.file : Int) + df).toNat < 8 ∧ ((s.rank : Int) + dr).toNat < 8 := by omega
    rw [dif_pos c2]
    apply congrArg some
    apply Fin.ext
    show ((s.rank : Int) + dr).toNat * 8 + ((s.file : Int) + df).toNat = t.val
    omega

theorem attacked_iff (b : Board) (s : Sq) (c : Color) :
    attacked b s c = true ↔ ∃ t pc, b t = some pc ∧ pc.color = c ∧ s ∈ attacks b t pc := by
  unfold attacked
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, -, h⟩
    cases hbt : b t with
    | none => rw [hbt] at h; simp at h
    | some pc =>
      rw [hbt] at h
      rw [Bool.and_eq_true, beq_iff_eq, List.contains_iff] at h
      exact ⟨t, pc, hbt, h.1, h.2⟩
  · rintro ⟨t, pc, hbt, hc, hs⟩
    exact ⟨t, List.mem_finRange t, by rw [hbt]; simp [hc, List.contains_iff, hs]⟩

theorem off_sqo_map (t : Sq) (df dr : Int) :
    (sqo ((fr t.val).1 + df) ((fr t.val).2 + dr)).map toSq = off t df dr := by
  have ef : (fr t.val).1 = (t.file : Int) := rfl
  have er : (fr t.val).2 = (t.rank : Int) := rfl
  have htf : t.file < 8 := Nat.mod_lt _ (by decide)
  have htr : t.rank < 8 := by have h := t.isLt; show t.val / 8 < 8; omega
  simp only [sqo, off, mkSq, ef, er]
  by_cases c : 0 ≤ (t.file : Int) + df ∧ (t.file : Int) + df < 8 ∧ 0 ≤ (t.rank : Int) + dr ∧ (t.rank : Int) + dr < 8
  · rw [if_pos c]
    have c1 : 0 ≤ (t.file : Int) + df ∧ 0 ≤ (t.rank : Int) + dr := ⟨c.1, c.2.2.1⟩
    have c2 : ((t.file : Int) + df).toNat < 8 ∧ ((t.rank : Int) + dr).toNat < 8 := by omega
    rw [if_pos c1, dif_pos c2]
    apply congrArg some
    apply Fin.ext
    show (((t.file : Int) + df) + 8 * ((t.rank : Int) + dr)).toNat % 64 =
      ((t.rank : Int) + dr).toNat * 8 + ((t.file : Int) + df).toNat
    omega
  · rw [if_neg c]
    by_cases c1 : 0 ≤ (t.file : Int) + df ∧ 0 ≤ (t.rank : Int) + dr
    · rw [if_pos c1]
      have c2 : ¬(((t.file : Int) + df).toNat < 8 ∧ ((t.rank : Int) + dr).toNat < 8) := by omega
      rw [dif_neg c2]
      rfl
    · rw [if_neg c1]
      rfl

theorem off_sqo_some (t s : Sq) (df dr : Int) :
    off t df dr = some s ↔ sqo ((fr t.val).1 + df) ((fr t.val).2 + dr) = some s.val := by
  rw [← off_sqo_map]
  constructor
  · intro h
    cases h2 : sqo ((fr t.val).1 + df) ((fr t.val).2 + dr) with
    | none => rw [h2] at h; simp at h
    | some v =>
      rw [h2] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hv : v < 64 := sqo_lt64 h2
      have ev : v = s.val := by
        have e := congrArg Fin.val h
        simp only [toSq] at e
        rw [Nat.mod_eq_of_lt hv] at e
        exact e
      rw [ev]
  · intro h
    rw [h]
    simp only [Option.map_some, toSq_val]

theorem rayGo_prefix (d : Int × Int) (m n : Nat) (v : Nat) : rayGo d m v <+: rayGo d (m + n) v := by
  induction m generalizing v with
  | zero => exact List.nil_prefix
  | succ m ih =>
    cases hgo : sqo ((fr v).1 + d.1) ((fr v).2 + d.2) with
    | none =>
      have e1 : rayGo d (m + 1) v = [] := by simp only [rayGo, hgo]
      have e2 : rayGo d (m + 1 + n) v = [] := by
        have hmn : m + 1 + n = (m + n) + 1 := by omega
        rw [hmn]
        simp only [rayGo, hgo]
      rw [e1, e2]
      exact List.prefix_rfl
    | some x =>
      have e1 : rayGo d (m + 1) v = x :: rayGo d m x := by simp only [rayGo, hgo]
      have e2 : rayGo d (m + 1 + n) v = x :: rayGo d (m + n) x := by
        have hmn : m + 1 + n = (m + n) + 1 := by omega
        rw [hmn]
        simp only [rayGo, hgo]
      rw [e1, e2, List.cons_prefix_cons]
      exact ⟨rfl, ih x⟩

theorem rayGo_eight : ∀ v ∈ List.range 64, ∀ d ∈ orth ++ diag, rayGo d 8 v = rayGo d 7 v := by
  decide +kernel

theorem mem_ray_iff (b : Board) (t s : Sq) (d : Int × Int) (n : Nat) :
    s ∈ ray b t d.1 d.2 n ↔ s.val ∈ rayGo d n t.val ∧
      ∀ w ∈ (rayGo d n t.val).takeWhile (· != s.val), b (toSq w) = none := by
  induction n generalizing t with
  | zero => simp [ray, rayGo]
  | succ n ih =>
    cases hgo : sqo ((fr t.val).1 + d.1) ((fr t.val).2 + d.2) with
    | none =>
      have hoff : off t d.1 d.2 = none := by rw [← off_sqo_map, hgo]; rfl
      have hg : rayGo d (n + 1) t.val = [] := by simp only [rayGo, hgo]
      have hray : ray b t d.1 d.2 (n + 1) = [] := by simp only [ray, hoff]
      simp [hray, hg]
    | some x =>
      have hx64 : x < 64 := sqo_lt64 hgo
      have hoff : off t d.1 d.2 = some (toSq x) := by rw [← off_sqo_map, hgo]; rfl
      have hval : (toSq x).val = x := toSq_val_of_lt x hx64
      have hg : rayGo d (n + 1) t.val = x :: rayGo d n x := by simp only [rayGo, hgo]
      cases he : empty b (toSq x) with
      | true =>
        have hray : ray b t d.1 d.2 (n + 1) = toSq x :: ray b (toSq x) d.1 d.2 n := by
          simp only [ray, hoff, he, if_true]
        have hbx : b (toSq x) = none := by
          have h2 : (b (toSq x)).isNone = true := he
          exact Option.isNone_iff_eq_none.mp h2
        rw [hray, hg, List.mem_cons, List.mem_cons]
        by_cases hsv : s.val = x
        · have hst : s = toSq x := by rw [← hval] at hsv; exact Fin.ext hsv
          subst hst
          refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => Or.inl rfl⟩
          · rw [hval]
            exact Or.inl rfl
          · rw [hval, List.takeWhile_cons_of_neg (by simp)]
            intro w hw
            simp at hw
        · have hne : s ≠ toSq x := fun e => hsv (hval ▸ congrArg Fin.val e)
          have hxtw : (x :: rayGo d n x).takeWhile (· != s.val) =
              x :: (rayGo d n x).takeWhile (· != s.val) :=
            List.takeWhile_cons_of_pos (bne_iff_ne.mpr (Ne.symm hsv))
          rw [hxtw, List.forall_mem_cons]
          constructor
          · rintro (h | h)
            · exact absurd h hne
            · obtain ⟨hm, ht⟩ := (ih (toSq x)).mp h
              rw [hval] at hm ht
              exact ⟨Or.inr hm, hbx, ht⟩
          · rintro ⟨hm, -, ht⟩
            rcases hm with hm | hm
            · exact absurd hm hsv
            · exact Or.inr ((ih (toSq x)).mpr ⟨by rw [hval]; exact hm, by rw [hval]; exact ht⟩)
      | false =>
        have hray : ray b t d.1 d.2 (n + 1) = [toSq x] := by
          simp only [ray, hoff, he, Bool.false_eq_true, if_false]
        have hbx : b (toSq x) ≠ none := by
          have h2 : (b (toSq x)).isNone = false := he
          intro e
          rw [e] at h2
          simp at h2
        rw [hray, hg]
        by_cases hsv : s.val = x
        · have hst : s = toSq x := by rw [← hval] at hsv; exact Fin.ext hsv
          subst hst
          refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => List.mem_singleton_self _⟩
          · rw [hval]
            exact List.mem_cons_self
          · rw [hval, List.takeWhile_cons_of_neg (by simp)]
            intro w hw
            simp at hw
        · have hne : s ≠ toSq x := fun e => hsv (hval ▸ congrArg Fin.val e)
          have hxtw : (x :: rayGo d n x).takeWhile (· != s.val) =
              x :: (rayGo d n x).takeWhile (· != s.val) :=
            List.takeWhile_cons_of_pos (bne_iff_ne.mpr (Ne.symm hsv))
          rw [hxtw, List.forall_mem_cons]
          constructor
          · intro h
            rw [List.mem_singleton] at h
            exact absurd h hne
          · rintro ⟨-, hxp, -⟩
            exact absurd hxp hbx

theorem sgn_cases (x : Int) : sgn x = 0 ∨ sgn x = 1 ∨ sgn x = -1 := by
  unfold sgn
  split
  · simp
  · split <;> simp

theorem sgn_eq_zero (x : Int) (h : sgn x = 0) : x = 0 := by
  unfold sgn at h
  split at h
  · omega
  · split at h
    · omega
    · omega

theorem direction_mem {a b : Nat} {d : Int × Int} (h : direction a b = some d) : d ∈ orth ++ diag := by
  simp only [direction] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i hne
      obtain rfl := Option.some.inj h
      rcases sgn_cases ((fr b).1 - (fr a).1) with h1 | h1 | h1 <;>
        rcases sgn_cases ((fr b).2 - (fr a).2) with h2 | h2 | h2
      · exfalso
        simp [sgn_eq_zero _ h1, sgn_eq_zero _ h2] at hne
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide

theorem mem_rays_iff (b : Board) (t s : Sq) (ds : List (Int × Int))
    (hsub : ∀ d ∈ ds, d ∈ orth ++ diag) :
    s ∈ rays b t ds ↔ ∃ d ∈ ds, direction t.val s.val = some d ∧
      ∀ u ∈ between t.val s.val, b (toSq u) = none := by
  show s ∈ ds.flatMap (fun (df, dr) => ray b t df dr 7) ↔ _
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨df, dr⟩, hd, hray⟩
    obtain ⟨hmem, htw⟩ := (mem_ray_iff b t s (df, dr) 7).mp hray
    have hsub' := hsub (df, dr) hd
    have h8 : s.val ∈ rayL t.val (df, dr) := (rayGo_prefix (df, dr) 7 1 t.val).subset hmem
    have hdir : direction t.val s.val = some (df, dr) :=
      (mem_rayL_iff t.val s.val t.isLt s.isLt _ hsub').mp h8
    refine ⟨(df, dr), hd, hdir, ?_⟩
    intro u hu
    have hc : (rayL t.val (df, dr)).contains s.val = true := List.contains_iff_mem.mpr h8
    have hbet : between t.val s.val = (rayL t.val (df, dr)).takeWhile (· != s.val) := by
      simp only [between, hdir, hc, ite_true]
    rw [hbet] at hu
    have h87 : rayL t.val (df, dr) = rayGo (df, dr) 7 t.val :=
      rayGo_eight t.val (List.mem_range.mpr t.isLt) _ hsub'
    rw [h87] at hu
    exact htw u hu
  · rintro ⟨⟨df, dr⟩, hd, hdir, hbtw⟩
    refine ⟨(df, dr), hd, ?_⟩
    have hsub' := hsub (df, dr) hd
    have h8 : s.val ∈ rayL t.val (df, dr) := (mem_rayL_iff t.val s.val t.isLt s.isLt _ hsub').mpr hdir
    have h87 : rayL t.val (df, dr) = rayGo (df, dr) 7 t.val :=
      rayGo_eight t.val (List.mem_range.mpr t.isLt) _ hsub'
    have hc : (rayL t.val (df, dr)).contains s.val = true := List.contains_iff_mem.mpr h8
    have hbet : between t.val s.val = (rayL t.val (df, dr)).takeWhile (· != s.val) := by
      simp only [between, hdir, hc, ite_true]
    apply (mem_ray_iff b t s (df, dr) 7).mpr
    refine ⟨h87 ▸ h8, fun w hw => ?_⟩
    rw [← h87, ← hbet] at hw
    exact hbtw w hw

theorem mem_attacks_slider (b : Board) (t s : Sq) (pc : Piece)
    (hk : pc.kind = .bishop ∨ pc.kind = .rook ∨ pc.kind = .queen) :
    s ∈ attacks b t pc ↔ ∃ d, direction t.val s.val = some d ∧
      ((pc.kind = .rook → d ∈ orth) ∧ (pc.kind = .bishop → d ∈ diag)) ∧
      ∀ u ∈ between t.val s.val, b (toSq u) = none := by
  rcases hk with hk | hk | hk
  · have hatt : attacks b t pc = rays b t bishopD := by simp only [attacks, hk]
    rw [hatt, mem_rays_iff b t s bishopD (fun d hd => List.mem_append.mpr (Or.inr hd))]
    constructor
    · rintro ⟨d, hd, hdir, hbtw⟩
      exact ⟨d, hdir, ⟨fun h => absurd (hk.symm.trans h) (by decide), fun _ => hd⟩, hbtw⟩
    · rintro ⟨d, hdir, ⟨-, hbi⟩, hbtw⟩
      exact ⟨d, hbi hk, hdir, hbtw⟩
  · have hatt : attacks b t pc = rays b t rookD := by simp only [attacks, hk]
    rw [hatt, mem_rays_iff b t s rookD (fun d hd => List.mem_append.mpr (Or.inl hd))]
    constructor
    · rintro ⟨d, hd, hdir, hbtw⟩
      exact ⟨d, hdir, ⟨fun _ => hd, fun h => absurd (hk.symm.trans h) (by decide)⟩, hbtw⟩
    · rintro ⟨d, hdir, ⟨hor, -⟩, hbtw⟩
      exact ⟨d, hor hk, hdir, hbtw⟩
  · have hatt : attacks b t pc = rays b t queenD := by simp only [attacks, hk]
    rw [hatt, mem_rays_iff b t s queenD (fun d hd => hd)]
    constructor
    · rintro ⟨d, hd, hdir, hbtw⟩
      exact ⟨d, hdir, ⟨fun h => absurd (hk.symm.trans h) (by decide),
        fun h => absurd (hk.symm.trans h) (by decide)⟩, hbtw⟩
    · rintro ⟨d, hdir, -, hbtw⟩
      exact ⟨d, direction_mem hdir, hdir, hbtw⟩

theorem mem_attacks_knight (b : Board) (t s : Sq) (c : Color) :
    s ∈ attacks b t ⟨c, .knight⟩ ↔ s.val ∈ knightL t.val := by
  have hmem : ∀ d : Int × Int, d ∈ knightD ↔ d ∈ kn := by
    intro d
    simp only [knightD, kn, List.mem_cons, List.mem_nil_iff, or_false]
    constructor <;> rintro (h | h | h | h | h | h | h | h) <;> subst h <;> decide
  show s ∈ steps t knightD ↔ s.val ∈ knightL t.val
  simp only [steps, knightL, List.mem_filterMap]
  constructor
  · rintro ⟨d, hd, hoff⟩
    obtain ⟨df, dr⟩ := d
    exact ⟨⟨df, dr⟩, (hmem _).mp hd, (off_sqo_some t s df dr).mp hoff⟩
  · rintro ⟨d, hd, hoff⟩
    obtain ⟨df, dr⟩ := d
    exact ⟨⟨df, dr⟩, (hmem _).mpr hd, (off_sqo_some t s df dr).mpr hoff⟩

theorem mem_attacks_pawn (b : Board) (t s : Sq) (c : Color) :
    s ∈ attacks b t ⟨c, .pawn⟩ ↔ (s.rank : Int) = t.rank + c.fwd ∧ ((s.file : Int) - t.file).natAbs = 1 := by
  show s ∈ steps t [(1, c.fwd), (-1, c.fwd)] ↔ _
  simp only [steps, List.mem_filterMap, List.mem_cons, List.mem_nil_iff, or_false]
  constructor
  · rintro ⟨⟨df, dr⟩, hd, hoff⟩
    obtain ⟨e1, e2⟩ := (off_eq_some t s df dr).mp hoff
    rcases hd with h | h
    · injection h with hdf hdr
      subst hdf; subst hdr
      refine ⟨e2, ?_⟩
      have : (s.file : Int) - t.file = 1 := by omega
      rw [this]
      rfl
    · injection h with hdf hdr
      subst hdf; subst hdr
      refine ⟨e2, ?_⟩
      have : (s.file : Int) - t.file = -1 := by omega
      rw [this]
      rfl
  · rintro ⟨hr, hf⟩
    have hdf : (s.file : Int) - t.file = 1 ∨ (s.file : Int) - t.file = -1 := by omega
    rcases hdf with hdf | hdf
    · exact ⟨(1, c.fwd), Or.inl rfl, (off_eq_some t s 1 c.fwd).mpr ⟨by omega, by omega⟩⟩
    · exact ⟨(-1, c.fwd), Or.inr rfl, (off_eq_some t s (-1) c.fwd).mpr ⟨by omega, by omega⟩⟩

theorem mem_attacks_king (b : Board) (t s : Sq) (c : Color) :
    s ∈ attacks b t ⟨c, .king⟩ ↔ cheb t.val s.val = 1 := by
  have hcheb : cheb t.val s.val =
      max (((t.file : Int) - s.file).natAbs) (((t.rank : Int) - s.rank).natAbs) := rfl
  simp only [attacks, steps, List.mem_filterMap]
  constructor
  · rintro ⟨⟨df, dr⟩, hd, hoff⟩
    obtain ⟨e1, e2⟩ := (off_eq_some t s df dr).mp hoff
    simp only [queenD, rookD, bishopD, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false, Prod.mk.injEq] at hd
    rcases hd with hd | hd <;> rcases hd with ⟨hdf, hdr⟩ | ⟨hdf, hdr⟩ | ⟨hdf, hdr⟩ | ⟨hdf, hdr⟩ <;>
      · subst hdf; subst hdr
        rw [hcheb]
        omega
  · intro h
    rw [hcheb] at h
    have h1 : (s.file : Int) - t.file = 0 ∨ (s.file : Int) - t.file = 1 ∨ (s.file : Int) - t.file = -1 := by omega
    have h2 : (s.rank : Int) - t.rank = 0 ∨ (s.rank : Int) - t.rank = 1 ∨ (s.rank : Int) - t.rank = -1 := by omega
    have hqueen : ∀ df dr : Int, (df, dr) ∈ queenD → df = (s.file : Int) - t.file →
        dr = (s.rank : Int) - t.rank → ∃ a, a ∈ queenD ∧ off t a.1 a.2 = some s := by
      intro df dr hd hdf hdr
      exact ⟨(df, dr), hd, (off_eq_some t s df dr).mpr ⟨by omega, by omega⟩⟩
    rcases h1 with hf | hf | hf <;> rcases h2 with hr | hr | hr
    · exfalso; omega
    · exact hqueen 0 1 (by decide) hf.symm hr.symm
    · exact hqueen 0 (-1) (by decide) hf.symm hr.symm
    · exact hqueen 1 0 (by decide) hf.symm hr.symm
    · exact hqueen 1 1 (by decide) hf.symm hr.symm
    · exact hqueen 1 (-1) (by decide) hf.symm hr.symm
    · exact hqueen (-1) 0 (by decide) hf.symm hr.symm
    · exact hqueen (-1) 1 (by decide) hf.symm hr.symm
    · exact hqueen (-1) (-1) (by decide) hf.symm hr.symm

theorem defs_mono {s s' : St} (h : Ext s s') {i : Nat} {d : VDef} (hd : s.defs[i]? = some d) :
    s'.defs[i]? = some d := by
  obtain ⟨hi, hd⟩ := Array.getElem?_eq_some_iff.mp hd
  exact (h.defs_eq _ hi).trans (congrArg some hd)

theorem layout_mono {c : Cfg} {s s' : St} (h : Ext s s') (hl : Layout c s) : Layout c s' := by
  intro q hq k hk
  obtain ⟨hpos, hd⟩ := hl q hq k hk
  exact ⟨hpos, defs_mono h hd⟩

theorem rightsOk_mono {c : Cfg} {s s' : St} {r : Rights} (h : Ext s s') (hr : RightsOk c s r) : RightsOk c s' r := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  refine ⟨?_, h2, ?_, h4⟩
  · intro f v hfv
    obtain ⟨hf, hvp, hd⟩ := h1 f v hfv
    exact ⟨hf, hvp, defs_mono h hd⟩
  · intro b v hbv
    obtain ⟨hvp, hd⟩ := h3 b v hbv
    exact ⟨hvp, defs_mono h hd⟩

theorem layout_bounded {c : Cfg} {s : St} (hs : Inv s) (hl : Layout c s) (q k : Nat) (hq : q ∈ c.squares) (hk : k < 11) :
    0 < (c.xv q k).natAbs ∧ (c.xv q k).natAbs ≤ s.nv := by
  obtain ⟨-, hd⟩ := hl q hq k hk
  obtain ⟨hi, -⟩ := Array.getElem?_eq_some_iff.mp hd
  have ht : (c.xv q k).toNat = 1 + 11 * c.xIdx q + k := Int.toNat_natCast _
  have ha : (c.xv q k).natAbs = 1 + 11 * c.xIdx q + k := Int.natAbs_natCast _
  rw [← hs.nv] at hi
  omega

theorem evalAny_append (A : Assignment) (es es' : List Ex) :
    Ex.evalAny A (es ++ es') = (Ex.evalAny A es || Ex.evalAny A es') := by
  induction es with
  | nil => simp [Ex.evalAny]
  | cons e es ih => simp [Ex.evalAny, ih, Bool.or_assoc]

theorem evalAny_true_iff (A : Assignment) (es : List Ex) :
    Ex.evalAny A es = true ↔ ∃ e ∈ es, e.eval A = true := by
  induction es with
  | nil => simp [Ex.evalAny]
  | cons e es ih =>
      simp only [Ex.evalAny, Bool.or_eq_true, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨e', h1, h2⟩)
        · exact ⟨e, Or.inl rfl, h⟩
        · exact ⟨e', Or.inr h1, h2⟩
      · rintro ⟨e', h1 | h2, h3⟩
        · subst h1
          exact Or.inl h3
        · exact Or.inr ⟨e', h2, h3⟩

theorem filterMap_congr {α β : Type} {f g : α → Option β} (h : ∀ a, f a = g a) :
    ∀ l : List α, l.filterMap f = l.filterMap g := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.filterMap_cons, List.filterMap_cons, h a, ih]

theorem evalAny_guard (A : Assignment) (emp occ excl : List Nat) (qs : List Nat) (E : Nat → Ex)
    (Cond : Nat → Prop) [∀ q, Decidable (Cond q)]
    (hE : ∀ q ∈ qs, (E q).eval A = decide (Cond q)) :
    Ex.evalAny A (qs.filterMap fun q =>
        if (q ∈ emp || q ∈ occ || q ∈ excl : Bool) then none else some (E q)) =
      decide (∃ q ∈ qs, q ∉ emp ∧ q ∉ occ ∧ q ∉ excl ∧ Cond q) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, evalAny_true_iff]
  constructor
  · rintro ⟨e, he, hev⟩
    rw [List.mem_filterMap] at he
    obtain ⟨q, hq, hqeq⟩ := he
    by_cases hbad : (q ∈ emp || q ∈ occ || q ∈ excl : Bool)
    · rw [if_pos hbad] at hqeq
      cases hqeq
    · rw [if_neg hbad] at hqeq
      cases hqeq
      have h1 : q ∉ emp := fun h => hbad (by simp only [h, decide_true, Bool.true_or])
      have h2 : q ∉ occ := fun h => hbad (by simp only [h, decide_true, Bool.true_or, Bool.or_true])
      have h3 : q ∉ excl := fun h => hbad (by simp only [h, decide_true, Bool.or_true])
      rw [hE q hq] at hev
      exact ⟨q, hq, h1, h2, h3, (decide_eq_true_iff).mp hev⟩
  · rintro ⟨q, hq, h1, h2, h3, h4⟩
    refine ⟨E q, ?_, ?_⟩
    · rw [List.mem_filterMap]
      refine ⟨q, hq, ?_⟩
      rw [if_neg (by simp [h1, h2, h3])]
    · rw [hE q hq]
      exact (decide_eq_true_iff).mpr h4

end Chess.All63

namespace Chess.All63

theorem mem_knightL_lt {s x : Nat} (h : x ∈ knightL s) : x < 64 := by
  simp only [knightL, List.mem_filterMap] at h
  obtain ⟨d, -, hd⟩ := h
  exact sqo_lt64 hd

theorem evalAny_flatMap {α : Type} (A : Assignment) (ds : List α) (f : α → List Ex) :
    Ex.evalAny A (ds.flatMap f) = true ↔ ∃ d ∈ ds, Ex.evalAny A (f d) = true := by
  induction ds with
  | nil => simp [Ex.evalAny]
  | cons d ds ih =>
      rw [List.flatMap_cons, evalAny_append, Bool.or_eq_true, ih]
      constructor
      · rintro (h | ⟨d', h1, h2⟩)
        · exact ⟨d, List.mem_cons_self, h⟩
        · exact ⟨d', List.mem_cons_of_mem d h1, h2⟩
      · rintro ⟨d', h1, h2⟩
        rw [List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact Or.inl h2
        · exact Or.inr ⟨d', h1, h2⟩

theorem file_toSq {q : Nat} (hq : q < 64) : (toSq q).file = q % 8 := by
  simp only [Sq.file, toSq_val_of_lt q hq]

theorem rank_toSq {q : Nat} (hq : q < 64) : (toSq q).rank = q / 8 := by
  simp only [Sq.rank, toSq_val_of_lt q hq]

theorem fr_fst {q : Nat} (hq : q < 64) : (fr q).1 = ((toSq q).file : Int) := by
  show ((q % 8 : Nat) : Int) = _
  rw [file_toSq hq]

theorem fr_snd {q : Nat} (hq : q < 64) : (fr q).2 = ((toSq q).rank : Int) := by
  show ((q / 8 : Nat) : Int) = _
  rw [rank_toSq hq]

theorem sqo_fr {f r : Int} {q : Nat} (h : sqo f r = some q) : (fr q).1 = f ∧ (fr q).2 = r := by
  by_cases g : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8
  · rw [sqo, if_pos g] at h
    have e : q = (f + 8 * r).toNat := (Option.some.inj h).symm
    subst e
    obtain ⟨hf0, hf1, hr0, hr1⟩ := g
    constructor
    · show (((f + 8 * r).toNat % 8 : Nat) : Int) = f
      have hd : (f + 8 * r).toNat % 8 = f.toNat := by omega
      rw [hd, Int.toNat_of_nonneg hf0]
    · show (((f + 8 * r).toNat / 8 : Nat) : Int) = r
      have hd : (f + 8 * r).toNat / 8 = r.toNat := by omega
      rw [hd, Int.toNat_of_nonneg hr0]
  · rw [sqo, if_neg g] at h
    exact absurd h (by simp)

theorem sqo_some {f r : Int} (hf : 0 ≤ f) (hf8 : f < 8) (hr : 0 ≤ r) (hr8 : r < 8) :
    sqo f r = some (f + 8 * r).toNat := by
  rw [sqo, if_pos ⟨hf, hf8, hr, hr8⟩]

theorem dir_tab : ∀ a ∈ List.range 64, ∀ b ∈ List.range 64,
    (direction a b).all (fun d =>
      decide (direction b a = some (-d.1, -d.2)) &&
      decide ((-d.1, -d.2) ∈ orth ++ diag) &&
      (decide (d ∈ orth) == decide ((-d.1, -d.2) ∈ orth)) &&
      (decide (d ∈ diag) == decide ((-d.1, -d.2) ∈ diag))) = true := by
  decide +kernel

theorem direction_neg {a b : Nat} (ha : a < 64) (hb : b < 64) {d : Int × Int}
    (h : direction a b = some d) :
    direction b a = some (-d.1, -d.2) ∧ (-d.1, -d.2) ∈ orth ++ diag ∧
      (d ∈ orth ↔ (-d.1, -d.2) ∈ orth) ∧ (d ∈ diag ↔ (-d.1, -d.2) ∈ diag) := by
  have t := (Option.all_eq_true _ _).mp
    (dir_tab a (List.mem_range.mpr ha) b (List.mem_range.mpr hb)) d h
  simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq, decide_eq_decide] at t
  exact ⟨t.1.1.1, t.1.1.2, t.1.2, t.2⟩

theorem orth_not_diag (d : Int × Int) (h : d ∈ orth) : d ∉ diag := by
  have : ∀ d ∈ orth, d ∉ diag := by decide
  exact this d h

theorem between_self_tab : ∀ a ∈ List.range 64, ∀ b ∈ List.range 64,
    (a ∉ between a b) ∧ (b ∉ between a b) := by
  decide +kernel

theorem not_mem_between_self {a b : Nat} (ha : a < 64) (hb : b < 64) :
    (a ∉ between a b) ∧ (b ∉ between a b) :=
  between_self_tab a (List.mem_range.mpr ha) b (List.mem_range.mpr hb)

theorem knight_cheb_tab : ∀ a ∈ List.range 64, ∀ b ∈ List.range 64,
    b ∈ knightL a → cheb a b ≤ 2 := by
  decide +kernel

theorem knight_cheb {a b : Nat} (ha : a < 64) (hb : b < 64) (h : b ∈ knightL a) :
    cheb a b ≤ 2 :=
  knight_cheb_tab a (List.mem_range.mpr ha) b (List.mem_range.mpr hb) h

end Chess.All63

namespace Chess.All63

theorem symOf_knight (o : Option Piece) (white : Bool) :
    (symOf o == (if white then 1 else 6)) = decide (o = some ⟨colOf white, .knight⟩) := by
  cases white <;> rcases o with _ | ⟨cl, kd⟩ <;> first | decide | (cases cl <;> cases kd <;> decide)

theorem symOf_pawn (o : Option Piece) (white : Bool) :
    (symOf o == (if white then 0 else 5)) = decide (o = some ⟨colOf white, .pawn⟩) := by
  cases white <;> rcases o with _ | ⟨cl, kd⟩ <;> first | decide | (cases cl <;> cases kd <;> decide)

theorem symOf_sl (o : Option Piece) (white : Bool) (d : Int × Int) :
    (((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5).contains
        (symOf o)) =
      decide (∃ pc, o = some pc ∧ pc.color = colOf white ∧
        (if d ∈ orth then (pc.kind = .rook ∨ pc.kind = .queen)
        else (pc.kind = .bishop ∨ pc.kind = .queen))) := by
  by_cases hd : d ∈ orth <;> cases white <;> rcases o with _ | ⟨cl, kd⟩ <;>
    (try cases cl) <;> (try cases kd) <;> simp [hd, symOf, colOf, kindIdx, EMP]

theorem clear_conv {p : Pos} {b' : Board} {K a : Nat} {emp occ excl : List Nat}
    (hd : ∀ q ∈ emp, q ∉ occ) (hx : ∀ q ∈ excl, q ∈ occ ∨ q = K) (hK : K ∉ between K a)
    (h1 : ∀ q ∈ between K a, q ∉ emp → q ∉ occ → q ∉ excl → b' (toSq q) = p.board (toSq q))
    (h2 : ∀ q ∈ between K a, q ∈ emp → b' (toSq q) = none)
    (h3 : ∀ q ∈ between K a, q ∈ occ → b' (toSq q) ≠ none) :
    (between K a).all (fun q => decide (q ∈ emp) || (!decide (q ∈ occ) && (p.board (toSq q)).isNone)) =
      decide (∀ q ∈ between K a, b' (toSq q) = none) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
  constructor
  · intro hall q hq
    have hmem := hall q hq
    by_cases he : q ∈ emp
    · exact h2 q hq he
    · simp only [he, decide_false, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, Option.isNone_iff_eq_none] at hmem
      have hxq : q ∉ excl := fun h => (hx q h).elim hmem.1 (fun h => hK (h ▸ hq))
      rw [h1 q hq he hmem.1 hxq]
      exact hmem.2
  · intro hbb q hq
    by_cases he : q ∈ emp
    · simp [he]
    · by_cases ho : q ∈ occ
      · exact absurd (hbb q hq) (h3 q hq ho)
      · have hxq : q ∉ excl := fun h => (hx q h).elim (fun h => ho h) (fun h => hK (h ▸ hq))
        have hp : p.board (toSq q) = none := by
          rw [← h1 q hq he ho hxq]
          exact hbb q hq
        simp [he, ho, hp]

section Semantics

variable {c : Cfg} {p : Pos} {A : Assignment} {s : St}

theorem nat_beq_of_ne (a b : Nat) (h : a ≠ b) : (a == b) = false := by
  apply Bool.eq_false_of_ne_true
  rw [beq_iff_eq]
  exact h

theorem eval_p (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (q k : Nat) (hq : q < 64) (hk : k < 11) :
    (c.p q k).eval A = (symOf (p.board (toSq q)) == k) := by
  by_cases hK : c.isK q = true
  · have hp : c.p q k = .k false := by simp only [Cfg.p, if_pos hK]
    rw [hp]
    obtain ⟨hwk, hbk, -⟩ := fits_kings hf
    unfold Cfg.isK at hK
    rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hK
    rcases hK with rfl | rfl
    · rw [hwk]
      show false = ((11 : Nat) == k)
      rw [nat_beq_of_ne 11 k (by omega)]
    · rw [hbk]
      show false = ((16 : Nat) == k)
      rw [nat_beq_of_ne 16 k (by omega)]
  · have he : c.isK q = false := Bool.eq_false_of_ne_true hK
    have hp : c.p q k = .v (c.xv q k) := by simp only [Cfg.p, if_neg hK]
    rw [hp]
    have hmem : q ∈ c.squares :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hq, by simp [he]⟩
    obtain ⟨hpos, hd⟩ := hl q hmem k hk
    obtain ⟨hi, hd2⟩ := Array.getElem?_eq_some_iff.mp hd
    have hA := hg _ hi
    rw [hd2] at hA
    show litVal A (c.xv q k) = _
    show (if 0 < c.xv q k then A (c.xv q k).toNat else !A (c.xv q k).natAbs) =
      (symOf (p.board (toSq q)) == k)
    rw [if_pos hpos]
    have ht : (c.xv q k).toNat = 1 + 11 * c.xIdx q + k := Int.toNat_natCast _
    have e : (c.xv q k).toNat - 1 + 1 = (c.xv q k).toNat := by omega
    rw [← e]
    exact hA

theorem eval_empty (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (q : Nat) (hq : q < 64) :
    (c.empty q).eval A = (p.board (toSq q)).isNone := by
  show (c.p q EMP).eval A = (p.board (toSq q)).isNone
  rw [eval_p hf hg hl q EMP hq (by decide)]
  match h : p.board (toSq q) with
  | none => rfl
  | some ⟨.white, .pawn⟩ => rfl
  | some ⟨.white, .knight⟩ => rfl
  | some ⟨.white, .bishop⟩ => rfl
  | some ⟨.white, .rook⟩ => rfl
  | some ⟨.white, .queen⟩ => rfl
  | some ⟨.white, .king⟩ => rfl
  | some ⟨.black, .pawn⟩ => rfl
  | some ⟨.black, .knight⟩ => rfl
  | some ⟨.black, .bishop⟩ => rfl
  | some ⟨.black, .rook⟩ => rfl
  | some ⟨.black, .queen⟩ => rfl
  | some ⟨.black, .king⟩ => rfl

theorem evalAny_map_p (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (q : Nat) (hq : q < 64)
    (ks : List Nat) (hks : ∀ k ∈ ks, k < 11) :
    Ex.evalAny A (ks.map (c.p q)) = ks.any fun k => (symOf (p.board (toSq q)) == k) := by
  revert hks
  induction ks with
  | nil => intro _; rfl
  | cons j ks ih =>
    intro hks
    rw [List.map_cons, List.any_cons]
    show ((c.p q j).eval A || Ex.evalAny A (ks.map (c.p q))) =
      ((symOf (p.board (toSq q)) == j) || ks.any fun k => (symOf (p.board (toSq q)) == k))
    rw [eval_p hf hg hl q j hq (hks j List.mem_cons_self),
      ih fun k hk => hks k (List.mem_cons_of_mem j hk)]

theorem eval_has (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (q : Nat) (hq : q < 64)
    (ks : List Nat) (hks : ∀ k ∈ ks, k < 11) :
    (c.has q ks).eval A = ks.contains (symOf (p.board (toSq q))) := by
  show Ex.evalAny A (ks.map (c.p q)) = ks.contains (symOf (p.board (toSq q)))
  rw [List.contains_eq_any_beq]
  exact evalAny_map_p hf hg hl q hq ks hks

theorem eval_wocc (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (q : Nat) (hq : q < 64) :
    (c.wocc q).eval A = (p.board (toSq q)).any (·.color == .white) := by
  obtain ⟨hwk, hbk, hsym⟩ := fits_kings hf
  by_cases hkw : (q == c.kw) = true
  · have hq2 : q = c.kw := beq_iff_eq.mp hkw
    subst hq2
    rw [show c.wocc c.kw = .k true from by simp [Cfg.wocc], hwk]
    rfl
  · have hkw' : (q == c.kw) = false := Bool.eq_false_of_ne_true hkw
    have hqk : q ≠ c.kw := by
      intro e
      subst e
      simp at hkw'
    rw [show c.wocc q = c.has q symW from by simp [Cfg.wocc, hkw'],
      eval_has hf hg hl q hq symW fun k hk => by
        simp only [symW, List.mem_cons, List.not_mem_nil, or_false] at hk
        omega]
    match h : p.board (toSq q) with
    | none => rfl
    | some ⟨.white, .pawn⟩ => rfl
    | some ⟨.white, .knight⟩ => rfl
    | some ⟨.white, .bishop⟩ => rfl
    | some ⟨.white, .rook⟩ => rfl
    | some ⟨.white, .queen⟩ => rfl
    | some ⟨.white, .king⟩ =>
      by_cases hkb : q = c.kb
      · subst hkb
        rw [h] at hbk
        exact absurd hbk (by decide)
      · have h1 := hsym q hq hqk hkb
        rw [h] at h1
        exact absurd h1 (by decide)
    | some ⟨.black, .pawn⟩ => rfl
    | some ⟨.black, .knight⟩ => rfl
    | some ⟨.black, .bishop⟩ => rfl
    | some ⟨.black, .rook⟩ => rfl
    | some ⟨.black, .queen⟩ => rfl
    | some ⟨.black, .king⟩ => rfl

theorem evalAll_map_empty (hf : Fits c p) (hg : Good p A s) (hl : Layout c s)
    (L : List Nat) (hL : ∀ q ∈ L, q < 64) :
    Ex.evalAll A (L.map c.empty) = L.all fun q => (p.board (toSq q)).isNone := by
  revert hL
  induction L with
  | nil => intro _; rfl
  | cons j L ih =>
    intro hL
    rw [List.map_cons, List.all_cons]
    show ((c.empty j).eval A && Ex.evalAll A (L.map c.empty)) =
      ((p.board (toSq j)).isNone && L.all fun q => (p.board (toSq q)).isNone)
    rw [eval_empty hf hg hl j (hL j List.mem_cons_self),
      ih fun k hk => hL k (List.mem_cons_of_mem j hk)]

theorem all_filter_between (L : List Nat) (emp occ : List Nat)
    (h : ∀ q ∈ L, q ∉ emp → q ∉ occ) :
    ((L.filter (· ∉ emp)).all fun q => (p.board (toSq q)).isNone) =
      L.all fun q => decide (q ∈ emp) || (!decide (q ∈ occ) && (p.board (toSq q)).isNone) := by
  revert h
  induction L with
  | nil => intro _; rfl
  | cons j L ih =>
    intro h
    rw [List.filter_cons]
    split
    · rename_i hdc
      have hqe : j ∉ emp := of_decide_eq_true hdc
      have hqo : j ∉ occ := h j List.mem_cons_self hqe
      simp only [List.all_cons, decide_eq_false_iff_not.mpr hqe, decide_eq_false_iff_not.mpr hqo,
        Bool.false_or, Bool.not_false, Bool.true_and, ih fun k hk hke => h k (List.mem_cons_of_mem j hk) hke]
    · rename_i hdc
      have hqe : j ∈ emp := by
        by_cases he : j ∈ emp
        · exact he
        · exact absurd (decide_eq_true_iff.mpr he) hdc
      simp only [List.all_cons, decide_eq_true_iff.mpr hqe, Bool.true_or, Bool.true_and]
      exact ih fun k hk hke => h k (List.mem_cons_of_mem j hk) hke

theorem eval_clear (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (a b : Nat) (ha : a < 64) (hb : b < 64)
    (emp occ : List Nat) :
    (c.clear a b emp occ).eval A =
      (between a b).all fun q => decide (q ∈ emp) || (!decide (q ∈ occ) && (p.board (toSq q)).isNone) := by
  show (if ((between a b).filter (· ∉ emp)).any (· ∈ occ) then Ex.k false
      else Ex.and (((between a b).filter (· ∉ emp)).map c.empty)).eval A =
      (between a b).all fun q => decide (q ∈ emp) || (!decide (q ∈ occ) && (p.board (toSq q)).isNone)
  by_cases hany : ((between a b).filter (· ∉ emp)).any (· ∈ occ) = true
  · rw [if_pos hany]
    obtain ⟨q, hqf, hqo⟩ := List.any_eq_true.mp hany
    obtain ⟨hqb, hqe⟩ := List.mem_filter.mp hqf
    have d1 : decide (q ∈ emp) = false := decide_eq_false_iff_not.mpr (of_decide_eq_true hqe)
    have d2 : decide (q ∈ occ) = true := decide_eq_true_iff.mpr (of_decide_eq_true hqo)
    have hf2 : (between a b).all (fun q => decide (q ∈ emp) ||
        (!decide (q ∈ occ) && (p.board (toSq q)).isNone)) = false := by
      rw [List.all_eq_false]
      exact ⟨q, hqb, by simp [d1, d2]⟩
    rw [hf2]
    rfl
  · have hnoocc : ∀ q ∈ between a b, q ∉ emp → q ∉ occ := by
      intro q hq hqe hqo
      have h2 : ((between a b).filter (· ∉ emp)).any (· ∈ occ) = true :=
        List.any_eq_true.mpr ⟨q, List.mem_filter.mpr ⟨hq, decide_eq_true_iff.mpr hqe⟩,
          show (fun x => decide (x ∈ occ)) q from decide_eq_true_iff.mpr hqo⟩
      rw [h2] at hany
      exact hany rfl
    rw [if_neg hany]
    show Ex.evalAll A (((between a b).filter (· ∉ emp)).map c.empty) =
      (between a b).all fun q => decide (q ∈ emp) || (!decide (q ∈ occ) && (p.board (toSq q)).isNone)
    rw [evalAll_map_empty hf hg hl _ fun q hq => between_lt64 (List.mem_filter.mp hq).1]
    rw [all_filter_between (between a b) emp occ hnoocc]



theorem eval_att_slider (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (K : Nat) (hK : K < 64)
    (white : Bool) (emp occ excl : List Nat) (b' : Board)
    (hb : Agrees p b' emp occ excl) (hexcl : ∀ q ∈ excl, q ∈ occ ∨ q = K) (hdisj : ∀ q ∈ emp, q ∉ occ)
    (hko : c.kb ∉ emp ++ occ) (hkw : c.kw ∉ occ) :
    Ex.evalAny A ((orth ++ diag).flatMap fun d =>
      (rayL K d).filterMap fun q =>
        if q ∈ emp || q ∈ occ || q ∈ excl then none
        else some (Ex.and [c.has q ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
          c.clear K q emp occ])) =
    decide (∃ t : Sq, t.val ∉ occ ++ excl ∧ ∃ pc, b' t = some pc ∧ pc.color = colOf white ∧
      (pc.kind = .bishop ∨ pc.kind = .rook ∨ pc.kind = .queen) ∧ toSq K ∈ attacks b' t pc) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, evalAny_flatMap]
  constructor
  · rintro ⟨d, hd, hdv⟩
    have hgu_d := evalAny_guard A emp occ excl (rayL K d)
      (fun q => Ex.and [c.has q ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
        c.clear K q emp occ])
      (fun q => (∃ pc, p.board (toSq q) = some pc ∧ pc.color = colOf white ∧
          (if d ∈ orth then (pc.kind = .rook ∨ pc.kind = .queen)
          else (pc.kind = .bishop ∨ pc.kind = .queen))) ∧
        ∀ u ∈ between K q, b' (toSq u) = none)
      (fun q hq => by
        have hq64 : q < 64 := rayL_lt64 hq
        have hks : ∀ k ∈ ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
            k < 11 := by
          by_cases hdo : d ∈ orth <;> cases white <;> simp [hdo] <;> decide
        have hae : (Ex.and [c.has q ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
              c.clear K q emp occ]).eval A =
            ((c.has q ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5)).eval A &&
              (c.clear K q emp occ).eval A) := by
          show (Ex.eval A (c.has q ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5)) &&
            (Ex.eval A (c.clear K q emp occ) && true)) = _
          cases Ex.eval A (c.has q ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5)) <;>
            cases Ex.eval A (c.clear K q emp occ) <;> rfl
        have hx : (c.has q ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5)).eval A =
            decide (∃ pc, p.board (toSq q) = some pc ∧ pc.color = colOf white ∧
              (if d ∈ orth then (pc.kind = .rook ∨ pc.kind = .queen)
              else (pc.kind = .bishop ∨ pc.kind = .queen))) := by
          rw [eval_has hf hg hl q hq64 _ hks, symOf_sl]
        have hy : (c.clear K q emp occ).eval A = decide (∀ u ∈ between K q, b' (toSq u) = none) := by
          rw [eval_clear hf hg hl K q hK hq64 emp occ,
            clear_conv hdisj hexcl (not_mem_between_self hK hq64).1
              (fun u hu h1 h2 h3 => hb.1 u (between_lt64 hu) h1 h2 h3)
              (fun u hu h2 => hb.2.1 u h2 (hdisj u h2))
              (fun u hu h3 => hb.2.2 u h3)]
        rw [hae, hx, hy, Bool.and_eq_decide]
        by_cases hP : (∃ pc, p.board (toSq q) = some pc ∧ pc.color = colOf white ∧
            (if d ∈ orth then (pc.kind = .rook ∨ pc.kind = .queen)
            else (pc.kind = .bishop ∨ pc.kind = .queen))) <;>
          by_cases hC : (∀ u ∈ between K q, b' (toSq u) = none) <;> simp [hP, hC])
    rw [hgu_d, decide_eq_true_iff] at hdv
    obtain ⟨q, hq, hne, hno, hnx, hPA, hcl⟩ := hdv
    obtain ⟨pc, hbpc, hcol, hkd⟩ := hPA
    have hq64 : q < 64 := rayL_lt64 hq
    have hdir : direction K q = some d := (mem_rayL_iff K q hK hq64 d hd).mp hq
    have hdneg := direction_neg hK hq64 hdir
    have hslider : pc.kind = .bishop ∨ pc.kind = .rook ∨ pc.kind = .queen := by
      by_cases hdo : d ∈ orth
      · rw [if_pos hdo] at hkd
        rcases hkd with h | h <;> simp [h]
      · rw [if_neg hdo] at hkd
        rcases hkd with h | h <;> simp [h]
    have hcompat : (pc.kind = .rook → (-d.1, -d.2) ∈ orth) ∧ (pc.kind = .bishop → (-d.1, -d.2) ∈ diag) := by
      by_cases hdo : d ∈ orth
      · rw [if_pos hdo] at hkd
        refine ⟨fun _ => hdneg.2.2.1.mp hdo, fun hbk => ?_⟩
        rcases hkd with h | h <;> rw [h] at hbk <;> cases hbk
      · have hdd : d ∈ diag := by
          rcases List.mem_append.mp hd with h | h
          · exact absurd h hdo
          · exact h
        rw [if_neg hdo] at hkd
        refine ⟨fun hr => ?_, fun _ => hdneg.2.2.2.mp hdd⟩
        rcases hkd with h | h <;> rw [h] at hr <;> cases hr
    have hd1 : direction (toSq q).val (toSq K).val = some (-d.1, -d.2) := by
      rw [toSq_val_of_lt q hq64, toSq_val_of_lt K hK]
      exact hdneg.1
    have hbetween : ∀ u ∈ between (toSq q).val (toSq K).val, b' (toSq u) = none := by
      rw [toSq_val_of_lt q hq64, toSq_val_of_lt K hK]
      intro u hu
      exact hcl u ((between_symm q K hq64 hK u).mp hu)
    have hatt : toSq K ∈ attacks b' (toSq q) pc :=
      (mem_attacks_slider b' (toSq q) (toSq K) pc hslider).mpr ⟨(-d.1, -d.2), hd1, hcompat, hbetween⟩
    refine ⟨toSq q, ?_, pc, ?_, hcol, hslider, hatt⟩
    · rw [toSq_val_of_lt q hq64, List.mem_append, not_or]
      exact ⟨hno, hnx⟩
    · rw [hb.1 q hq64 hne hno hnx]
      exact hbpc
  · rintro ⟨t, ht, pc, hbt, hcol, hslider, hatt⟩
    rw [List.mem_append, not_or] at ht
    obtain ⟨hno, hnx⟩ := ht
    have hq64 : t.val < 64 := t.isLt
    obtain ⟨d', hd', hcomp, hbtw⟩ := (mem_attacks_slider b' t (toSq K) pc hslider).mp hatt
    have hKval : (toSq K).val = K := toSq_val_of_lt K hK
    rw [hKval] at hd' hbtw
    have hdneg := direction_neg hq64 hK hd'
    have hne : t.val ∉ emp := fun h => by
      have h4 := hb.2.1 t.val h hno
      rw [toSq_val] at h4
      rw [h4] at hbt
      contradiction
    have hpbd : p.board (toSq t.val) = some pc := by
      have h5 := hb.1 t.val hq64 hne hno hnx
      rw [toSq_val] at h5 ⊢
      rw [← h5]
      exact hbt
    have hkc : (if (-d'.1, -d'.2) ∈ orth then (pc.kind = .rook ∨ pc.kind = .queen)
        else (pc.kind = .bishop ∨ pc.kind = .queen)) := by
      rcases hslider with h | h | h
      · have hdia : d' ∈ diag := hcomp.2 h
        have hno' : (-d'.1, -d'.2) ∉ orth := fun hor =>
          orth_not_diag d' (hdneg.2.2.1.mpr hor) hdia
        rw [if_neg hno']
        exact Or.inl h
      · have hor : d' ∈ orth := hcomp.1 h
        rw [if_pos (hdneg.2.2.1.mp hor)]
        exact Or.inl h
      · by_cases ho : (-d'.1, -d'.2) ∈ orth
        · rw [if_pos ho]
          exact Or.inr h
        · rw [if_neg ho]
          exact Or.inr h
    have hcl' : ∀ u ∈ between K t.val, b' (toSq u) = none := fun u hu =>
      hbtw u ((between_symm K t.val hK hq64 u).mp hu)
    refine ⟨(-d'.1, -d'.2), hdneg.2.1, ?_⟩
    show Ex.evalAny A ((rayL K (-d'.1, -d'.2)).filterMap fun q =>
      if q ∈ emp || q ∈ occ || q ∈ excl then none
      else some (Ex.and [c.has q ((if (-d'.1, -d'.2) ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
        c.clear K q emp occ])) = true
    rw [evalAny_guard A emp occ excl (rayL K (-d'.1, -d'.2))
      (fun q => Ex.and [c.has q ((if (-d'.1, -d'.2) ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
        c.clear K q emp occ])
      (fun q => (∃ pc, p.board (toSq q) = some pc ∧ pc.color = colOf white ∧
          (if (-d'.1, -d'.2) ∈ orth then (pc.kind = .rook ∨ pc.kind = .queen)
          else (pc.kind = .bishop ∨ pc.kind = .queen))) ∧
        ∀ u ∈ between K q, b' (toSq u) = none)
      (fun q hq => by
        have hq164 : q < 64 := rayL_lt64 hq
        have hks : ∀ k ∈ ((if (-d'.1, -d'.2) ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
            k < 11 := by
          by_cases hdo : (-d'.1, -d'.2) ∈ orth <;> cases white <;> simp [hdo] <;> decide
        have hae : (Ex.and [c.has q ((if (-d'.1, -d'.2) ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
              c.clear K q emp occ]).eval A =
            ((c.has q ((if (-d'.1, -d'.2) ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5)).eval A &&
              (c.clear K q emp occ).eval A) := by
          show (Ex.eval A (c.has q ((if (-d'.1, -d'.2) ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5)) &&
            (Ex.eval A (c.clear K q emp occ) && true)) = _
          cases Ex.eval A (c.has q ((if (-d'.1, -d'.2) ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5)) <;>
            cases Ex.eval A (c.clear K q emp occ) <;> rfl
        have hx : (c.has q ((if (-d'.1, -d'.2) ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5)).eval A =
            decide (∃ pc, p.board (toSq q) = some pc ∧ pc.color = colOf white ∧
              (if (-d'.1, -d'.2) ∈ orth then (pc.kind = .rook ∨ pc.kind = .queen)
              else (pc.kind = .bishop ∨ pc.kind = .queen))) := by
          rw [eval_has hf hg hl q hq164 _ hks, symOf_sl]
        have hy : (c.clear K q emp occ).eval A = decide (∀ u ∈ between K q, b' (toSq u) = none) := by
          rw [eval_clear hf hg hl K q hK hq164 emp occ,
            clear_conv hdisj hexcl (not_mem_between_self hK hq164).1
              (fun u hu h1 h2 h3 => hb.1 u (between_lt64 hu) h1 h2 h3)
              (fun u hu h2 => hb.2.1 u h2 (hdisj u h2))
              (fun u hu h3 => hb.2.2 u h3)]
        rw [hae, hx, hy, Bool.and_eq_decide]
        by_cases hP : (∃ pc, p.board (toSq q) = some pc ∧ pc.color = colOf white ∧
            (if (-d'.1, -d'.2) ∈ orth then (pc.kind = .rook ∨ pc.kind = .queen)
            else (pc.kind = .bishop ∨ pc.kind = .queen))) <;>
          by_cases hC : (∀ u ∈ between K q, b' (toSq u) = none) <;> simp [hP, hC])]
    rw [decide_eq_true_iff]
    exact ⟨t.val, (mem_rayL_iff K t.val hK hq64 (-d'.1, -d'.2) hdneg.2.1).mpr hdneg.1,
      hne, hno, hnx, ⟨pc, hpbd, hcol, hkc⟩, hcl'⟩


theorem eval_att_knight (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (K : Nat) (hK : K < 64)
    (white : Bool) (emp occ excl : List Nat) (b' : Board)
    (hb : Agrees p b' emp occ excl) (hexcl : ∀ q ∈ excl, q ∈ occ ∨ q = K) (hdisj : ∀ q ∈ emp, q ∉ occ)
    (hko : c.kb ∉ emp ++ occ) (hkw : c.kw ∉ occ) :
    Ex.evalAny A ((knightL K).filterMap fun q =>
        if q ∈ emp || q ∈ occ || q ∈ excl then none else some (c.p q (if white then 1 else 6))) =
    decide (∃ t : Sq, t.val ∉ occ ++ excl ∧ b' t = some ⟨colOf white, .knight⟩ ∧
      toSq K ∈ attacks b' t ⟨colOf white, .knight⟩) := by
  have hgu := evalAny_guard A emp occ excl (knightL K)
    (fun q => c.p q (if white then 1 else 6))
    (fun q => p.board (toSq q) = some ⟨colOf white, .knight⟩)
    (fun q hq => by
      rw [eval_p hf hg hl q _ (mem_knightL_lt hq) (by cases white <;> decide), symOf_knight])
  rw [hgu, decide_eq_decide]
  constructor
  · rintro ⟨q, hq, hne, hno, hnx, hpc⟩
    refine ⟨toSq q, ?_, ?_, ?_⟩
    · rw [toSq_val_of_lt q (mem_knightL_lt hq), List.mem_append, not_or]
      exact ⟨hno, hnx⟩
    · rw [hb.1 q (mem_knightL_lt hq) hne hno hnx]
      exact hpc
    · have h2 : K ∈ knightL q := (mem_knightL_symm K q hK (mem_knightL_lt hq)).mpr hq
      have h3 : (toSq K).val ∈ knightL (toSq q).val := by
        rw [toSq_val_of_lt K hK, toSq_val_of_lt q (mem_knightL_lt hq)]
        exact h2
      exact (mem_attacks_knight b' (toSq q) (toSq K) (colOf white)).mpr h3
  · rintro ⟨t, ht, hbt, hatt⟩
    rw [List.mem_append, not_or] at ht
    obtain ⟨hno, hnx⟩ := ht
    have h2 : K ∈ knightL t.val := by
      have h3 := (mem_attacks_knight b' t (toSq K) (colOf white)).mp hatt
      rwa [toSq_val_of_lt K hK] at h3
    have hq : t.val ∈ knightL K := (mem_knightL_symm K t.val hK t.isLt).mp h2
    have hne : t.val ∉ emp := fun h => by
      have h4 := hb.2.1 t.val h hno
      rw [toSq_val] at h4
      rw [h4] at hbt
      contradiction
    refine ⟨t.val, hq, hne, hno, hnx, ?_⟩
    have h5 := hb.1 t.val t.isLt hne hno hnx
    rw [toSq_val] at h5 ⊢
    rw [← h5]
    exact hbt


theorem eval_att_pawn (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (K : Nat) (hK : K < 64)
    (white : Bool) (emp occ excl : List Nat) (b' : Board)
    (hb : Agrees p b' emp occ excl) (hexcl : ∀ q ∈ excl, q ∈ occ ∨ q = K) (hdisj : ∀ q ∈ emp, q ∉ occ)
    (hko : c.kb ∉ emp ++ occ) (hkw : c.kw ∉ occ) :
    Ex.evalAny A ([(-1 : Int), 1].filterMap fun df =>
        match sqo ((fr K).1 + df) (if white then (fr K).2 - 1 else (fr K).2 + 1) with
        | some q => if q ∈ emp || q ∈ occ || q ∈ excl then none else some (c.p q (if white then 0 else 5))
        | none => none) =
    decide (∃ t : Sq, t.val ∉ occ ++ excl ∧ b' t = some ⟨colOf white, .pawn⟩ ∧
      toSq K ∈ attacks b' t ⟨colOf white, .pawn⟩) := by
  have hlist : ([(-1 : Int), 1].filterMap fun df =>
      match sqo ((fr K).1 + df) (if white then (fr K).2 - 1 else (fr K).2 + 1) with
      | some q => if q ∈ emp || q ∈ occ || q ∈ excl then none else some (c.p q (if white then 0 else 5))
      | none => none) =
    (([(-1 : Int), 1].filterMap fun df =>
      sqo ((fr K).1 + df) (if white then (fr K).2 - 1 else (fr K).2 + 1)).filterMap fun q =>
      if q ∈ emp || q ∈ occ || q ∈ excl then none else some (c.p q (if white then 0 else 5))) := by
    rw [List.filterMap_filterMap]
    refine filterMap_congr (fun df => ?_) _
    cases sqo ((fr K).1 + df) (if white then (fr K).2 - 1 else (fr K).2 + 1) <;> rfl
  have hqs64 : ∀ q ∈ ([(-1 : Int), 1].filterMap fun df =>
      sqo ((fr K).1 + df) (if white then (fr K).2 - 1 else (fr K).2 + 1)), q < 64 := by
    intro q hq
    rw [List.mem_filterMap] at hq
    obtain ⟨df, -, hq⟩ := hq
    exact sqo_lt64 hq
  have hgu := evalAny_guard A emp occ excl
    ([(-1 : Int), 1].filterMap fun df =>
      sqo ((fr K).1 + df) (if white then (fr K).2 - 1 else (fr K).2 + 1))
    (fun q => c.p q (if white then 0 else 5))
    (fun q => p.board (toSq q) = some ⟨colOf white, .pawn⟩)
    (fun q hq => by
      rw [eval_p hf hg hl q _ (hqs64 q hq) (by cases white <;> decide), symOf_pawn])
  rw [hlist, hgu, decide_eq_decide]
  constructor
  · rintro ⟨q, hq, hne, hno, hnx, hpc⟩
    rw [List.mem_filterMap] at hq
    obtain ⟨df, hdf, hqo⟩ := hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdf
    have hq64 : q < 64 := sqo_lt64 hqo
    refine ⟨toSq q, ?_, ?_, ?_⟩
    · rw [toSq_val_of_lt q hq64, List.mem_append, not_or]
      exact ⟨hno, hnx⟩
    · rw [hb.1 q hq64 hne hno hnx]
      exact hpc
    · rw [mem_attacks_pawn, ← fr_snd hK, ← fr_snd hq64, ← fr_fst hK, ← fr_fst hq64]
      rcases hdf with rfl | rfl <;> have hfrq := sqo_fr hqo <;> cases white <;>
        simp [colOf, Color.fwd] at hfrq ⊢ <;> omega
  · rintro ⟨t, ht, hbt, hatt⟩
    rw [List.mem_append, not_or] at ht
    obtain ⟨hno, hnx⟩ := ht
    have hq64 : t.val < 64 := t.isLt
    have hatt' : toSq K ∈ attacks b' (toSq t.val) ⟨colOf white, .pawn⟩ := by rwa [toSq_val]
    have hatt2 := (mem_attacks_pawn b' (toSq t.val) (toSq K) (colOf white)).mp hatt'
    rw [← fr_snd hK, ← fr_snd hq64, ← fr_fst hK, ← fr_fst hq64] at hatt2
    obtain ⟨hrk, hfl⟩ := hatt2
    have hdf2 : (fr t.val).1 - (fr K).1 = -1 ∨ (fr t.val).1 - (fr K).1 = 1 := by omega
    have hfr1 : 0 ≤ (fr t.val).1 ∧ (fr t.val).1 < 8 := by
      have e : (fr t.val).1 = ((t.val % 8 : Nat) : Int) := rfl
      rw [e]
      omega
    have hfr2 : 0 ≤ (fr t.val).2 ∧ (fr t.val).2 < 8 := by
      have e : (fr t.val).2 = ((t.val / 8 : Nat) : Int) := rfl
      rw [e]
      omega
    have hqmem : t.val ∈ ([(-1 : Int), 1].filterMap fun df =>
        sqo ((fr K).1 + df) (if white then (fr K).2 - 1 else (fr K).2 + 1)) := by
      rw [List.mem_filterMap]
      rcases hdf2 with h | h
      · refine ⟨-1, by decide, ?_⟩
        have hb1 : (fr t.val).1 = (fr K).1 + (-1) := by omega
        have hb2 : (fr t.val).2 = (if white then (fr K).2 - 1 else (fr K).2 + 1) := by
          cases white <;> simp [colOf, Color.fwd] at hrk ⊢ <;> omega
        rw [← hb1, ← hb2, sqo_some hfr1.1 hfr1.2 hfr2.1 hfr2.2]
        congr 1
        have e1 : (fr t.val).1 = ((t.val % 8 : Nat) : Int) := rfl
        have e2 : (fr t.val).2 = ((t.val / 8 : Nat) : Int) := rfl
        rw [e1, e2]
        omega
      · refine ⟨1, by decide, ?_⟩
        have hb1 : (fr t.val).1 = (fr K).1 + 1 := by omega
        have hb2 : (fr t.val).2 = (if white then (fr K).2 - 1 else (fr K).2 + 1) := by
          cases white <;> simp [colOf, Color.fwd] at hrk ⊢ <;> omega
        rw [← hb1, ← hb2, sqo_some hfr1.1 hfr1.2 hfr2.1 hfr2.2]
        congr 1
        have e1 : (fr t.val).1 = ((t.val % 8 : Nat) : Int) := rfl
        have e2 : (fr t.val).2 = ((t.val / 8 : Nat) : Int) := rfl
        rw [e1, e2]
        omega
    have hne : t.val ∉ emp := fun h => by
      have h4 := hb.2.1 t.val h hno
      rw [toSq_val] at h4
      rw [h4] at hbt
      contradiction
    refine ⟨t.val, hqmem, hne, hno, hnx, ?_⟩
    have h5 := hb.1 t.val hq64 hne hno hnx
    rw [toSq_val] at h5 ⊢
    rw [← h5]
    exact hbt


theorem eval_att (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (K : Nat) (hK : K < 64)
    (white : Bool) (k : Nat) (hk64 : k < 64) (emp occ excl : List Nat) (b' : Board)
    (hb : Agrees p b' emp occ excl) (hexcl : ∀ q ∈ excl, q ∈ occ ∨ q = K) (hdisj : ∀ q ∈ emp, q ∉ occ)
    (hemp : ∀ q ∈ emp, q < 64) (hocc : ∀ q ∈ occ, q < 64)
    (hk : ∀ t : Sq, b' t = some ⟨colOf white, .king⟩ ↔ t = toSq k) (hkx : cheb k K = 1 → k ∉ occ ++ excl)
    (hko : c.kb ∉ emp ++ occ) (hkw : c.kw ∉ occ) :
    (c.att K white k emp occ excl).eval A = decide (∃ t : Sq, t.val ∉ occ ++ excl ∧
      ∃ pc, b' t = some pc ∧ pc.color = colOf white ∧ toSq K ∈ attacks b' t pc) := by
  have h3 := eval_att_slider hf hg hl K hK white emp occ excl b' hb hexcl hdisj hko hkw
  have h1 := eval_att_knight hf hg hl K hK white emp occ excl b' hb hexcl hdisj hko hkw
  have h2 := eval_att_pawn hf hg hl K hK white emp occ excl b' hb hexcl hdisj hko hkw
  have hkg : Ex.evalAny A (if cheb k K == 1 then [.k true] else []) = (cheb k K == 1) := by
    by_cases h : cheb k K = 1 <;> simp [h, Ex.evalAny, Ex.eval]
  rw [show Cfg.att c K white k emp occ excl =
      Ex.or (((orth ++ diag).flatMap fun d =>
          (rayL K d).filterMap fun q =>
            if q ∈ emp || q ∈ occ || q ∈ excl then none
            else some (Ex.and
              [c.has q ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
                c.clear K q emp occ])) ++
        ((knightL K).filterMap fun q =>
          if q ∈ emp || q ∈ occ || q ∈ excl then none else some (c.p q (if white then 1 else 6))) ++
        ([(-1 : Int), 1].filterMap fun df =>
          match sqo ((fr K).1 + df) (if white then (fr K).2 - 1 else (fr K).2 + 1) with
          | some q =>
            if q ∈ emp || q ∈ occ || q ∈ excl then none else some (c.p q (if white then 0 else 5))
          | none => none) ++
        if cheb k K == 1 then [Ex.k true] else []) from rfl]
  show Ex.evalAny A (((orth ++ diag).flatMap fun d =>
        (rayL K d).filterMap fun q =>
          if q ∈ emp || q ∈ occ || q ∈ excl then none
          else some (Ex.and
            [c.has q ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
              c.clear K q emp occ])) ++
      ((knightL K).filterMap fun q =>
        if q ∈ emp || q ∈ occ || q ∈ excl then none else some (c.p q (if white then 1 else 6))) ++
      ([(-1 : Int), 1].filterMap fun df =>
        match sqo ((fr K).1 + df) (if white then (fr K).2 - 1 else (fr K).2 + 1) with
        | some q =>
          if q ∈ emp || q ∈ occ || q ∈ excl then none else some (c.p q (if white then 0 else 5))
        | none => none) ++
      if cheb k K == 1 then [Ex.k true] else []) = _
  rw [evalAny_append, evalAny_append, evalAny_append, h3, h1, h2, hkg]
  have hsort : (∃ t : Sq, t.val ∉ occ ++ excl ∧ ∃ pc, b' t = some pc ∧ pc.color = colOf white ∧
      toSq K ∈ attacks b' t pc) ↔
      (((∃ t : Sq, t.val ∉ occ ++ excl ∧ ∃ pc, b' t = some pc ∧ pc.color = colOf white ∧
          (pc.kind = .bishop ∨ pc.kind = .rook ∨ pc.kind = .queen) ∧ toSq K ∈ attacks b' t pc) ∨
        (∃ t : Sq, t.val ∉ occ ++ excl ∧ b' t = some ⟨colOf white, .knight⟩ ∧
          toSq K ∈ attacks b' t ⟨colOf white, .knight⟩)) ∨
        (∃ t : Sq, t.val ∉ occ ++ excl ∧ b' t = some ⟨colOf white, .pawn⟩ ∧
          toSq K ∈ attacks b' t ⟨colOf white, .pawn⟩)) ∨
      cheb k K = 1 := by
    constructor
    · rintro ⟨t, ht, pc, hbt, hcol, hatt⟩
      obtain ⟨cl, kd⟩ := pc
      subst hcol
      cases kd with
      | pawn => exact Or.inl (Or.inr ⟨t, ht, hbt, hatt⟩)
      | knight => exact Or.inl (Or.inl (Or.inr ⟨t, ht, hbt, hatt⟩))
      | bishop => exact Or.inl (Or.inl (Or.inl ⟨t, ht, ⟨colOf white, .bishop⟩, hbt, rfl, Or.inl rfl, hatt⟩))
      | rook => exact Or.inl (Or.inl (Or.inl ⟨t, ht, ⟨colOf white, .rook⟩, hbt, rfl, Or.inr (Or.inl rfl), hatt⟩))
      | queen => exact Or.inl (Or.inl (Or.inl ⟨t, ht, ⟨colOf white, .queen⟩, hbt, rfl, Or.inr (Or.inr rfl), hatt⟩))
      | king =>
          have h1' : cheb t.val K = 1 := by
            have h := (mem_attacks_king b' t (toSq K) (colOf white)).mp hatt
            rwa [toSq_val_of_lt K hK] at h
          have h2' : t = toSq k := (hk t).mp hbt
          have h3' : t.val = k := by rw [h2', toSq_val_of_lt k hk64]
          exact Or.inr (h3' ▸ h1')
    · intro h
      rcases h with ((h | h) | h) | h
      · obtain ⟨t, ht, pc, hbt, hcol, -, hatt⟩ := h
        exact ⟨t, ht, pc, hbt, hcol, hatt⟩
      · obtain ⟨t, ht, hbt, hatt⟩ := h
        exact ⟨t, ht, ⟨colOf white, .knight⟩, hbt, rfl, hatt⟩
      · obtain ⟨t, ht, hbt, hatt⟩ := h
        exact ⟨t, ht, ⟨colOf white, .pawn⟩, hbt, rfl, hatt⟩
      · refine ⟨toSq k, ?_, ⟨colOf white, .king⟩, ?_, rfl, ?_⟩
        · rw [toSq_val_of_lt k hk64]
          exact hkx h
        · exact (hk (toSq k)).mpr rfl
        · exact (mem_attacks_king b' (toSq k) (toSq K) (colOf white)).mpr (by
            rw [toSq_val_of_lt k hk64, toSq_val_of_lt K hK]
            exact h)
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Bool.or_eq_true, decide_eq_true_iff, beq_iff_eq]
  exact hsort.symm

theorem eval_direct (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (t T : Nat) (ht : t < 64) (hT : T ≤ 4)
    (emp occ : List Nat) (b' : Board) (hdisj : ∀ q ∈ emp, q ∉ occ)
    (hb : ∀ q ∈ between t c.kb, q ∉ emp → q ∉ occ → b' (toSq q) = p.board (toSq q))
    (he : ∀ q ∈ between t c.kb, q ∈ emp → q ∉ occ → b' (toSq q) = none)
    (ho : ∀ q ∈ between t c.kb, q ∈ occ → b' (toSq q) ≠ none) :
    (c.direct t T emp occ).eval A = (attacks b' (toSq t) ⟨.white, kindOf T⟩).contains (toSq c.kb) := by
  have hcfg := fits_cfgOk hf
  obtain ⟨hkw64, hkb64, -⟩ := hcfg
  have hcc : (between t c.kb).all (fun q => decide (q ∈ emp) || (!decide (q ∈ occ) && (p.board (toSq q)).isNone)) =
      decide (∀ q ∈ between t c.kb, b' (toSq q) = none) :=
    clear_conv hdisj (fun q hq => absurd hq List.not_mem_nil) (not_mem_between_self ht hkb64).1
      (fun q hq h1 h2 _ => hb q hq h1 h2) (fun q hq h2 => he q hq h2 (hdisj q h2)) ho
  show (if T == 1 then Ex.k (decide (cheb t c.kb ≤ 2) && (knightL t).contains c.kb)
      else if T == 0 then Ex.k ((fr c.kb).2 == (fr t).2 + 1 && ((fr c.kb).1 - (fr t).1).natAbs == 1)
      else match direction t c.kb with
        | none => Ex.k false
        | some d => if (T == 3 && decide (d ∉ orth) || T == 2 && decide (d ∉ diag)) then Ex.k false
          else c.clear t c.kb emp occ).eval A = _
  by_cases h1 : (T == 1) = true
  · rw [if_pos h1]
    have hT1 : T = 1 := beq_iff_eq.mp h1
    subst hT1
    show (Ex.k (decide (cheb t c.kb ≤ 2) && (knightL t).contains c.kb)).eval A =
        (attacks b' (toSq t) ⟨.white, .knight⟩).contains (toSq c.kb)
    show (decide (cheb t c.kb ≤ 2) && (knightL t).contains c.kb) = _
    rw [Bool.eq_iff_iff, List.contains_iff_mem]
    constructor
    · intro h
      rw [Bool.and_eq_true] at h
      have hm : c.kb ∈ knightL t := List.contains_iff_mem.mp h.2
      exact (mem_attacks_knight b' (toSq t) (toSq c.kb) .white).mpr (by
        rw [toSq_val_of_lt _ hkb64, toSq_val_of_lt t ht]
        exact hm)
    · intro h
      have hm := (mem_attacks_knight b' (toSq t) (toSq c.kb) .white).mp h
      rw [toSq_val_of_lt _ hkb64, toSq_val_of_lt t ht] at hm
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true_iff.mpr (knight_cheb ht hkb64 hm), List.contains_iff_mem.mpr hm⟩
  · rw [if_neg h1]
    by_cases h0 : (T == 0) = true
    · rw [if_pos h0]
      have hT0 : T = 0 := beq_iff_eq.mp h0
      subst hT0
      show (Ex.k ((fr c.kb).2 == (fr t).2 + 1 && ((fr c.kb).1 - (fr t).1).natAbs == 1)).eval A =
          (attacks b' (toSq t) ⟨.white, .pawn⟩).contains (toSq c.kb)
      show ((fr c.kb).2 == (fr t).2 + 1 && ((fr c.kb).1 - (fr t).1).natAbs == 1) = _
      rw [Bool.eq_iff_iff, List.contains_iff_mem, mem_attacks_pawn b' (toSq t) (toSq c.kb) .white,
        ← fr_snd hkb64, ← fr_snd ht, ← fr_fst hkb64, ← fr_fst ht]
      rw [show Color.white.fwd = (1 : Int) from rfl]
      constructor
      · intro h
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
        exact h
      · intro h
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
        exact h
    · rw [if_neg h0]
      have hn1 : T ≠ 1 := fun e => h1 (beq_iff_eq.mpr e)
      have hn0 : T ≠ 0 := fun e => h0 (beq_iff_eq.mpr e)
      have hT234 : T = 2 ∨ T = 3 ∨ T = 4 := by omega
      rcases hT234 with rfl | rfl | rfl
      · show (match direction t c.kb with
          | none => Ex.k false
          | some d => if (2 == 3 && decide (d ∉ orth) || 2 == 2 && decide (d ∉ diag)) then Ex.k false
            else c.clear t c.kb emp occ).eval A =
            (attacks b' (toSq t) ⟨.white, .bishop⟩).contains (toSq c.kb)
        split
        · rename_i hdir
          have hbc : (attacks b' (toSq t) ⟨.white, .bishop⟩).contains (toSq c.kb) = false := by
            cases hcb : (attacks b' (toSq t) ⟨.white, .bishop⟩).contains (toSq c.kb)
            · rfl
            exfalso
            rw [List.contains_iff_mem] at hcb
            obtain ⟨d', hd', -, -⟩ := (mem_attacks_slider b' (toSq t) (toSq c.kb) ⟨.white, .bishop⟩
              (Or.inl rfl)).mp hcb
            rw [toSq_val_of_lt t ht, toSq_val_of_lt _ hkb64] at hd'
            rw [hdir] at hd'
            cases hd'
          simp only [hbc, Ex.eval]
        · rename_i d hdir
          have hgw : (if (2 == 3 && decide (d ∉ orth) || 2 == 2 && decide (d ∉ diag)) then Ex.k false
              else c.clear t c.kb emp occ) =
              (if d ∈ diag then c.clear t c.kb emp occ else Ex.k false) := by
            by_cases hd : d ∈ diag <;> simp [hd]
          rw [hgw]
          by_cases hdB : d ∈ diag
          · rw [if_pos hdB]
            show (c.clear t c.kb emp occ).eval A = _
            rw [eval_clear hf hg hl t c.kb ht hkb64 emp occ, hcc, Bool.eq_iff_iff, decide_eq_true_iff,
              List.contains_iff_mem,
              mem_attacks_slider b' (toSq t) (toSq c.kb) ⟨.white, .bishop⟩ (Or.inl rfl),
              toSq_val_of_lt t ht, toSq_val_of_lt c.kb hkb64]
            constructor
            · intro hP
              exact ⟨d, hdir, ⟨fun h => absurd h (by decide), fun _ => hdB⟩, hP⟩
            · rintro ⟨d', hd', -, hP⟩
              have hdd : d = d' := by rw [hdir] at hd'; exact Option.some.inj hd'
              subst hdd
              exact hP
          · rw [if_neg hdB]
            have hbc : (attacks b' (toSq t) ⟨.white, .bishop⟩).contains (toSq c.kb) = false := by
              cases hcb : (attacks b' (toSq t) ⟨.white, .bishop⟩).contains (toSq c.kb)
              · rfl
              exfalso
              rw [List.contains_iff_mem] at hcb
              obtain ⟨d', hd', hcomp, -⟩ := (mem_attacks_slider b' (toSq t) (toSq c.kb) ⟨.white, .bishop⟩
                (Or.inl rfl)).mp hcb
              rw [toSq_val_of_lt t ht, toSq_val_of_lt _ hkb64] at hd'
              have hdd : d = d' := by rw [hdir] at hd'; exact Option.some.inj hd'
              subst hdd
              exact hdB (hcomp.2 rfl)
            simp only [hbc, Ex.eval]
      · show (match direction t c.kb with
          | none => Ex.k false
          | some d => if (3 == 3 && decide (d ∉ orth) || 3 == 2 && decide (d ∉ diag)) then Ex.k false
            else c.clear t c.kb emp occ).eval A =
            (attacks b' (toSq t) ⟨.white, .rook⟩).contains (toSq c.kb)
        split
        · rename_i hdir
          have hbc : (attacks b' (toSq t) ⟨.white, .rook⟩).contains (toSq c.kb) = false := by
            cases hcb : (attacks b' (toSq t) ⟨.white, .rook⟩).contains (toSq c.kb)
            · rfl
            exfalso
            rw [List.contains_iff_mem] at hcb
            obtain ⟨d', hd', -, -⟩ := (mem_attacks_slider b' (toSq t) (toSq c.kb) ⟨.white, .rook⟩
              (Or.inr (Or.inl rfl))).mp hcb
            rw [toSq_val_of_lt t ht, toSq_val_of_lt _ hkb64] at hd'
            rw [hdir] at hd'
            cases hd'
          simp only [hbc, Ex.eval]
        · rename_i d hdir
          have hgw : (if (3 == 3 && decide (d ∉ orth) || 3 == 2 && decide (d ∉ diag)) then Ex.k false
              else c.clear t c.kb emp occ) =
              (if d ∈ orth then c.clear t c.kb emp occ else Ex.k false) := by
            by_cases hd : d ∈ orth <;> simp [hd]
          rw [hgw]
          by_cases hdO : d ∈ orth
          · rw [if_pos hdO]
            show (c.clear t c.kb emp occ).eval A = _
            rw [eval_clear hf hg hl t c.kb ht hkb64 emp occ, hcc, Bool.eq_iff_iff, decide_eq_true_iff,
              List.contains_iff_mem,
              mem_attacks_slider b' (toSq t) (toSq c.kb) ⟨.white, .rook⟩ (Or.inr (Or.inl rfl)),
              toSq_val_of_lt t ht, toSq_val_of_lt c.kb hkb64]
            constructor
            · intro hP
              exact ⟨d, hdir, ⟨fun _ => hdO, fun h => absurd h (by decide)⟩, hP⟩
            · rintro ⟨d', hd', -, hP⟩
              have hdd : d = d' := by rw [hdir] at hd'; exact Option.some.inj hd'
              subst hdd
              exact hP
          · rw [if_neg hdO]
            have hbc : (attacks b' (toSq t) ⟨.white, .rook⟩).contains (toSq c.kb) = false := by
              cases hcb : (attacks b' (toSq t) ⟨.white, .rook⟩).contains (toSq c.kb)
              · rfl
              exfalso
              rw [List.contains_iff_mem] at hcb
              obtain ⟨d', hd', hcomp, -⟩ := (mem_attacks_slider b' (toSq t) (toSq c.kb) ⟨.white, .rook⟩
                (Or.inr (Or.inl rfl))).mp hcb
              rw [toSq_val_of_lt t ht, toSq_val_of_lt _ hkb64] at hd'
              have hdd : d = d' := by rw [hdir] at hd'; exact Option.some.inj hd'
              subst hdd
              exact hdO (hcomp.1 rfl)
            simp only [hbc, Ex.eval]
      · show (match direction t c.kb with
          | none => Ex.k false
          | some d => if (4 == 3 && decide (d ∉ orth) || 4 == 2 && decide (d ∉ diag)) then Ex.k false
            else c.clear t c.kb emp occ).eval A =
            (attacks b' (toSq t) ⟨.white, .queen⟩).contains (toSq c.kb)
        split
        · rename_i hdir
          have hbc : (attacks b' (toSq t) ⟨.white, .queen⟩).contains (toSq c.kb) = false := by
            cases hcb : (attacks b' (toSq t) ⟨.white, .queen⟩).contains (toSq c.kb)
            · rfl
            exfalso
            rw [List.contains_iff_mem] at hcb
            obtain ⟨d', hd', -, -⟩ := (mem_attacks_slider b' (toSq t) (toSq c.kb) ⟨.white, .queen⟩
              (Or.inr (Or.inr rfl))).mp hcb
            rw [toSq_val_of_lt t ht, toSq_val_of_lt _ hkb64] at hd'
            rw [hdir] at hd'
            cases hd'
          simp only [hbc, Ex.eval]
        · rename_i d hdir
          have hgw : (if (4 == 3 && decide (d ∉ orth) || 4 == 2 && decide (d ∉ diag)) then Ex.k false
              else c.clear t c.kb emp occ) = c.clear t c.kb emp occ := by
            simp
          rw [hgw]
          show (c.clear t c.kb emp occ).eval A = _
          rw [eval_clear hf hg hl t c.kb ht hkb64 emp occ, hcc, Bool.eq_iff_iff, decide_eq_true_iff,
            List.contains_iff_mem,
            mem_attacks_slider b' (toSq t) (toSq c.kb) ⟨.white, .queen⟩ (Or.inr (Or.inr rfl)),
            toSq_val_of_lt t ht, toSq_val_of_lt c.kb hkb64]
          constructor
          · intro hP
            exact ⟨d, hdir, ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, hP⟩
          · rintro ⟨d', hd', -, hP⟩
            have hdd : d = d' := by rw [hdir] at hd'; exact Option.some.inj hd'
            subst hdd
            exact hP


end Semantics

def Cand.IsMk (c : Cfg) (m : Cand) : Prop := m = c.mkMove m.src m.dst m.promo m.T m.pseudo m.ep m.w

def Cand.KindOk (p : Pos) (m : Cand) : Prop :=
  isCastle p m.mv = false ∧
    match m.ep with
    | none => isEp p m.mv = false
    | some e => isEp p m.mv = true ∧ e = (epVictim m.mv).val

section Cands

variable {c : Cfg} {p : Pos} {A : Assignment} {s : St} {r : Rights}

theorem sqo_lt {f r : Int} {x : Nat} (h : sqo f r = some x) : x < 64 := by
  by_cases g : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8
  · rw [sqo, if_pos g] at h
    have h2 : (f + 8 * r).toNat = x := Option.some.inj h
    subst h2
    obtain ⟨hf0, hf1, hr0, hr1⟩ := g
    omega
  · rw [sqo, if_neg g] at h
    exact absurd h (by simp)

theorem sqo_snd {f r : Int} {x : Nat} (h : sqo f r = some x) : (fr x).snd = r := by
  by_cases g : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8
  · rw [sqo, if_pos g] at h
    have h2 : (f + 8 * r).toNat = x := Option.some.inj h
    subst h2
    obtain ⟨hf0, hf1, hr0, hr1⟩ := g
    have hd : (f + 8 * r).toNat / 8 = r.toNat := by omega
    show (((f + 8 * r).toNat / 8 : Nat) : Int) = r
    rw [hd]
    exact Int.toNat_of_nonneg hr0
  · rw [sqo, if_neg g] at h
    exact absurd h (by simp)

theorem sqo_getD_lt (f r : Int) : ((sqo f r).getD 0) < 64 := by
  by_cases g : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8
  · rw [sqo, if_pos g, Option.getD_some]
    obtain ⟨hf0, hf1, hr0, hr1⟩ := g
    omega
  · rw [sqo, if_neg g, Option.getD_none]
    decide

theorem rayGo_lt {d : Int × Int} (n s x : Nat) (h : x ∈ rayGo d n s) : x < 64 := by
  induction n generalizing s with
  | zero => simp [rayGo] at h
  | succ n ih =>
    simp only [rayGo] at h
    split at h
    · simp at h
    · next y hy =>
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · exact sqo_lt hy
      · exact ih _ h

theorem mem_rayL_lt {s x : Nat} {d : Int × Int} (h : x ∈ rayL s d) : x < 64 := rayGo_lt 8 s x h


theorem mem_flatMap_rayL_lt {q x : Nat} {ds : List (Int × Int)} (h : x ∈ ds.flatMap (rayL q)) : x < 64 := by
  simp only [List.mem_flatMap] at h
  obtain ⟨d, -, hd⟩ := h
  exact mem_rayL_lt hd

theorem mem_targets_lt {q T x : Nat} (h : x ∈ c.targets q T) : x < 64 := by
  have h2 : x ∈ List.filter (fun t => !c.isK t) (if T == 1 then knightL q
      else (if T == 3 then orth else if T == 2 then diag else orth ++ diag).flatMap (rayL q)) := h
  have h := (List.mem_filter.mp h2).1
  split at h
  · exact mem_knightL_lt h
  · split at h
    · exact mem_flatMap_rayL_lt h
    · split at h
      · exact mem_flatMap_rayL_lt h
      · exact mem_flatMap_rayL_lt h

theorem mkMove_IsMk (q t : Nat) (pr : Option Nat) (T : Nat) (ps : Ex) (ep : Option Nat) (w : Nat) :
    Cand.IsMk c (c.mkMove q t pr T ps ep w) := rfl

theorem mkPawn_mk (q t : Nat) (ps : Ex) (m : Cand) (hm : m ∈ c.mkPawn q t ps) :
    m.IsMk c ∧ m.src = q ∧ m.dst = t ∧ m.T = 0 ∧ (∀ k, m.promo = some k → 1 ≤ k ∧ k ≤ 4) ∧
      (m.promo.isSome ↔ (fr m.dst).2 = 7) ∧
      (m.w = if m.promo.isNone then 1 else if m.promo = some 1 then 4 else 0) := by
  simp only [Cfg.mkPawn] at hm
  split at hm
  · next h7 =>
    have h7' : (fr t).snd = 7 := beq_iff_eq.mp h7
    simp only [List.mem_map] at hm
    obtain ⟨⟨T, w⟩, hTw, rfl⟩ := hm
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hTw
    rcases hTw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨mkMove_IsMk q t (some 1) 0 ps none 4, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · intro k hk
        have hk2 : (some 1 : Option Nat) = some k := hk
        injection hk2 with e
        subst e
        decide
      · show (some 1 : Option Nat).isSome ↔ (fr t).snd = 7
        exact iff_of_true rfl h7'
      · show (4 : Nat) = if (some 1 : Option Nat).isNone then 1 else if (some 1 : Option Nat) = some 1 then 4 else 0
        decide
    · refine ⟨mkMove_IsMk q t (some 2) 0 ps none 0, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · intro k hk
        have hk2 : (some 2 : Option Nat) = some k := hk
        injection hk2 with e
        subst e
        decide
      · show (some 2 : Option Nat).isSome ↔ (fr t).snd = 7
        exact iff_of_true rfl h7'
      · show (0 : Nat) = if (some 2 : Option Nat).isNone then 1 else if (some 2 : Option Nat) = some 1 then 4 else 0
        decide
    · refine ⟨mkMove_IsMk q t (some 3) 0 ps none 0, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · intro k hk
        have hk2 : (some 3 : Option Nat) = some k := hk
        injection hk2 with e
        subst e
        decide
      · show (some 3 : Option Nat).isSome ↔ (fr t).snd = 7
        exact iff_of_true rfl h7'
      · show (0 : Nat) = if (some 3 : Option Nat).isNone then 1 else if (some 3 : Option Nat) = some 1 then 4 else 0
        decide
    · refine ⟨mkMove_IsMk q t (some 4) 0 ps none 0, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · intro k hk
        have hk2 : (some 4 : Option Nat) = some k := hk
        injection hk2 with e
        subst e
        decide
      · show (some 4 : Option Nat).isSome ↔ (fr t).snd = 7
        exact iff_of_true rfl h7'
      · show (0 : Nat) = if (some 4 : Option Nat).isNone then 1 else if (some 4 : Option Nat) = some 1 then 4 else 0
        decide
  · next h7 =>
    have h7' : (fr t).snd ≠ 7 := fun he => h7 (beq_iff_eq.mpr he)
    simp only [List.mem_singleton] at hm
    subst hm
    refine ⟨mkMove_IsMk q t none 0 ps none 1, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro k hk
      have hk2 : (none : Option Nat) = some k := hk
      cases hk2
    · show (none : Option Nat).isSome ↔ (fr t).snd = 7
      exact iff_of_false (by decide) h7'
    · show (1 : Nat) = if (none : Option Nat).isNone then 1 else if (none : Option Nat) = some 1 then 4 else 0
      decide

theorem mem_cands (m : Cand) : m ∈ c.cands r ↔
    (∃ q ∈ c.squares, m ∈ c.pieceCands q ∨ m ∈ c.pawnCands r q) ∨ m ∈ c.kingCands ∨ m ∈ c.castleCands r := by
  simp only [Cfg.cands, List.mem_append, List.mem_flatMap, or_assoc]

theorem pieceCands_mk (q : Nat) (hq : q ∈ c.squares) (m : Cand) (hm : m ∈ c.pieceCands q) :
    m.IsMk c ∧ m.src = q ∧ m.dst < 64 ∧ 1 ≤ m.T ∧ m.T ≤ 4 ∧ m.promo = none ∧ m.ep = none ∧ m.w = 1 := by
  simp only [Cfg.pieceCands, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨T, hT, t, ht, rfl⟩ := hm
  have hT' : 1 ≤ T ∧ T ≤ 4 := by
    simp at hT
    omega
  exact ⟨mkMove_IsMk q t none T _ none 1, rfl, mem_targets_lt ht, hT'.1, hT'.2, rfl, rfl, rfl⟩

theorem pawnCands_mk (q : Nat) (hq : q ∈ c.squares) (m : Cand) (hm : m ∈ c.pawnCands r q) :
    m.IsMk c ∧ m.src = q ∧ m.dst < 64 ∧ m.T = 0 ∧ (∀ k, m.promo = some k → 1 ≤ k ∧ k ≤ 4) ∧
      (m.promo.isSome ↔ (fr m.dst).2 = 7) ∧ (m.w = if m.promo.isNone then 1 else if m.promo = some 1 then 4 else 0) := by
  simp only [Cfg.pawnCands] at hm
  split at hm
  · simp at hm
  · simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · split at hm
      · simp at hm
      · simp only [List.mem_append] at hm
        rcases hm with hm | hm
        · obtain ⟨hmk, hsrc, hdst, hT, hpr, his, hw⟩ := mkPawn_mk q _ _ m hm
          exact ⟨hmk, hsrc, hdst ▸ sqo_getD_lt _ _, hT, hpr, his, hw⟩
        · split at hm
          · obtain ⟨hmk, hsrc, hdst, hT, hpr, his, hw⟩ := mkPawn_mk q _ _ m hm
            exact ⟨hmk, hsrc, hdst ▸ sqo_getD_lt _ _, hT, hpr, his, hw⟩
          · simp at hm
    · simp only [List.mem_flatMap] at hm
      obtain ⟨df, -, hm⟩ := hm
      split at hm
      · simp at hm
      · next t' ht =>
        split at hm
        · simp at hm
        · simp only [List.mem_append] at hm
          rcases hm with hm | hm
          · obtain ⟨hmk, hsrc, hdst, hT, hpr, his, hw⟩ := mkPawn_mk q _ _ m hm
            exact ⟨hmk, hsrc, hdst ▸ sqo_lt ht, hT, hpr, his, hw⟩
          · split at hm
            · next v hv =>
              simp only [List.mem_singleton] at hm
              subst hm
              have h4 : (fr q).snd = 4 := by
                by_cases hc : ((fr q).snd == 4) = true
                · exact beq_iff_eq.mp hc
                · exfalso
                  rw [if_neg hc] at hv
                  exact absurd hv (by simp)
              refine ⟨mkMove_IsMk q t' none 0 _ _ 1, rfl, sqo_lt ht, rfl, ?_, ?_, ?_⟩
              · intro k hk
                have hk2 : (none : Option Nat) = some k := hk
                cases hk2
              · show (none : Option Nat).isSome ↔ (fr t').snd = 7
                refine iff_of_false (by decide) ?_
                rw [sqo_snd ht, h4]
                decide
              · show (1 : Nat) = if (none : Option Nat).isNone then 1 else if (none : Option Nat) = some 1 then 4 else 0
                decide
            · simp at hm

theorem eval_and2 (A : Assignment) (a b : Ex) :
    (Ex.and [a, b]).eval A = (a.eval A && b.eval A) := by simp [Ex.eval, Ex.evalAll]

theorem eval_and3 (A : Assignment) (a b d : Ex) :
    (Ex.and [a, b, d]).eval A = (a.eval A && (b.eval A && d.eval A)) := by simp [Ex.eval, Ex.evalAll]

theorem mem_pseudo_of (p : Pos) (s : Sq) (pc : Piece) (m : Move)
    (hb : p.board s = some pc) (hc : pc.color = p.turn) (hm : m ∈ pieceMoves p s pc) :
    m ∈ pseudo p := by
  rw [pseudo, List.mem_append]
  exact .inl (List.mem_flatMap.mpr ⟨s, List.mem_finRange s, by
    simp only [hb, beq_iff_eq.mpr hc, ite_true]
    exact hm⟩)

theorem symOf_decode (o : Option Piece) (T : Nat) (hT : T ≤ 4) :
    (symOf o == T) = decide (o = some ⟨.white, kindOf T⟩) := by
  match T, hT with
  | 0, _ => rcases o with _ | ⟨cl, kd⟩ <;> first | decide | (cases cl <;> cases kd <;> decide)
  | 1, _ => rcases o with _ | ⟨cl, kd⟩ <;> first | decide | (cases cl <;> cases kd <;> decide)
  | 2, _ => rcases o with _ | ⟨cl, kd⟩ <;> first | decide | (cases cl <;> cases kd <;> decide)
  | 3, _ => rcases o with _ | ⟨cl, kd⟩ <;> first | decide | (cases cl <;> cases kd <;> decide)
  | 4, _ => rcases o with _ | ⟨cl, kd⟩ <;> first | decide | (cases cl <;> cases kd <;> decide)
  | T + 5, _ => exact absurd hT (by omega)

theorem symOf_mem_symB {o : Option Piece} (h : symOf o ∈ symB) :
    ∃ kd, o = some ⟨.black, kd⟩ := by
  rcases o with _ | ⟨cl, kd⟩
  · simp [symB, symOf, EMP] at h
  · cases cl with
    | white => cases kd <;> simp [symB, symOf, kindIdx] at h
    | black =>
      cases kd with
      | pawn => exact ⟨.pawn, rfl⟩
      | knight => exact ⟨.knight, rfl⟩
      | bishop => exact ⟨.bishop, rfl⟩
      | rook => exact ⟨.rook, rfl⟩
      | queen => exact ⟨.queen, rfl⟩
      | king => simp [symB, symOf, kindIdx] at h

theorem kindOf_ne_king (T : Nat) (hT : T ≤ 4) : kindOf T ≠ .king := by
  match T, hT with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | T + 5, _ => exact absurd hT (by omega)

theorem kindOf_ne_pawn (T : Nat) (hT1 : 1 ≤ T) (hT4 : T ≤ 4) : kindOf T ≠ .pawn := by
  match T, hT1, hT4 with
  | 0, _, _ => omega
  | 1, _, _ => decide
  | 2, _, _ => decide
  | 3, _, _ => decide
  | 4, _, _ => decide
  | T + 5, _, _ => omega

theorem kindOf_promos (T : Nat) (hT1 : 1 ≤ T) (hT4 : T ≤ 4) :
    kindOf T ∈ [Kind.knight, .bishop, .rook, .queen] := by
  match T, hT1, hT4 with
  | 0, _, _ => omega
  | 1, _, _ => decide
  | 2, _, _ => decide
  | 3, _, _ => decide
  | 4, _, _ => decide
  | T + 5, _, _ => omega

theorem off_of_sqo (q : Nat) (hq : q < 64) (df dr : Int) {u : Nat}
    (h : sqo ((fr q).1 + df) ((fr q).2 + dr) = some u) :
    off (toSq q) df dr = some (toSq u) := by
  have hv : (toSq q).val = q := toSq_val_of_lt q hq
  have h2 := off_sqo_map (toSq q) df dr
  rw [hv, h, Option.map_some] at h2
  exact h2.symm

theorem fr_bounds (q : Nat) (hq : q < 64) :
    0 ≤ (fr q).1 ∧ (fr q).1 < 8 ∧ 0 ≤ (fr q).2 ∧ (fr q).2 < 8 := by
  unfold fr
  omega

theorem sqo_bounds {f r : Int} {x : Nat} (h : sqo f r = some x) :
    0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8 ∧ x = (f + 8 * r).toNat := by
  by_cases g : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8
  · rw [sqo, if_pos g] at h
    exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2, (Option.some.inj h).symm⟩
  · rw [sqo, if_neg g] at h
    exact absurd h (by simp)

theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) {k : α} {v : β}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons a l ih =>
    obtain ⟨a1, a2⟩ := a
    rw [List.lookup] at h
    split at h
    · next hk =>
      have hk' : a1 = k := (beq_iff_eq.mp hk).symm
      obtain rfl := Option.some.inj h
      subst hk'
      exact List.mem_cons_self
    · next hk =>
      exact List.mem_cons_of_mem _ (ih h)

theorem kindOk_of_none (p : Pos) (m : Cand) (hmep : m.ep = none)
    (hcastle : isCastle p m.mv = false) (hep : isEp p m.mv = false) : m.KindOk p := by
  unfold Cand.KindOk
  rw [hmep]
  exact ⟨hcastle, hep⟩

theorem kindOk_ep (p : Pos) (m : Cand) (e : Nat)
    (hmep : m.ep = some e)
    (hcastle : isCastle p m.mv = false)
    (hep : isEp p m.mv = true) (hev : e = (epVictim m.mv).val) : m.KindOk p := by
  unfold Cand.KindOk
  rw [hmep]
  exact ⟨hcastle, hep, hev⟩

theorem isCastle_false_of_kind (p : Pos) (m : Move) {k : Kind} (hk : (k == .king) = false)
    (hb : p.board m.src = some ⟨.white, k⟩) : isCastle p m = false := by
  rw [isCastle, hb, Option.any_some, hk, Bool.false_and]

theorem isEp_false_of_kind (p : Pos) (m : Move) {k : Kind} (hk : (k == .pawn) = false)
    (hb : p.board m.src = some ⟨.white, k⟩) : isEp p m = false := by
  rw [isEp, hb, Option.any_some, hk, Bool.false_and, Bool.false_and]


theorem isEp_false_of_same_file (p : Pos) (m : Move) (hb : p.board m.src = some ⟨.white, .pawn⟩)
    (hf : m.src.file = m.dst.file) : isEp p m = false := by
  rw [isEp, hb, Option.any_some]
  rw [show ((Kind.pawn : Kind) == .pawn) = true from rfl, Bool.true_and]
  rw [show (m.src.file != m.dst.file) = false from by simp [hf], Bool.false_and]

theorem isEp_false_of_dst_some (p : Pos) (m : Move) {pc : Piece} (hb : p.board m.dst = some pc) :
    isEp p m = false := by
  have he : empty p.board m.dst = false := by rw [empty, hb]; rfl
  rw [isEp, he, Bool.and_false]

theorem mem_pieceMoves_of_attacks (p : Pos) (s : Sq) (q' : Piece) (hk : q'.kind ≠ .pawn) (t : Sq)
    (hatt : t ∈ attacks p.board s q')
    (hfoe : (p.board t).any (fun a => a.color == q'.color) = false) :
    ⟨s, t, none⟩ ∈ pieceMoves p s q' := by
  obtain ⟨qc, qk⟩ := q'
  cases qk with
  | pawn => exact absurd rfl hk
  | knight =>
    show (⟨s, t, none⟩ : Move) ∈ ((attacks p.board s ⟨qc, .knight⟩).filter
        fun t => !(p.board t).any (·.color == (⟨qc, .knight⟩ : Piece).color)).map fun t => ⟨s, t, none⟩
    exact List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨hatt, by simp [hfoe]⟩, rfl⟩
  | bishop =>
    show (⟨s, t, none⟩ : Move) ∈ ((attacks p.board s ⟨qc, .bishop⟩).filter
        fun t => !(p.board t).any (·.color == (⟨qc, .bishop⟩ : Piece).color)).map fun t => ⟨s, t, none⟩
    exact List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨hatt, by simp [hfoe]⟩, rfl⟩
  | rook =>
    show (⟨s, t, none⟩ : Move) ∈ ((attacks p.board s ⟨qc, .rook⟩).filter
        fun t => !(p.board t).any (·.color == (⟨qc, .rook⟩ : Piece).color)).map fun t => ⟨s, t, none⟩
    exact List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨hatt, by simp [hfoe]⟩, rfl⟩
  | queen =>
    show (⟨s, t, none⟩ : Move) ∈ ((attacks p.board s ⟨qc, .queen⟩).filter
        fun t => !(p.board t).any (·.color == (⟨qc, .queen⟩ : Piece).color)).map fun t => ⟨s, t, none⟩
    exact List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨hatt, by simp [hfoe]⟩, rfl⟩
  | king =>
    show (⟨s, t, none⟩ : Move) ∈ ((attacks p.board s ⟨qc, .king⟩).filter
        fun t => !(p.board t).any (·.color == (⟨qc, .king⟩ : Piece).color)).map fun t => ⟨s, t, none⟩
    exact List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨hatt, by simp [hfoe]⟩, rfl⟩

theorem pawnMoves_mk_aux (p : Pos) (s t : Sq) (pr : Option Kind)
    (hpr : (t.rank = 7 → ∃ k, k ∈ [Kind.knight, .bishop, .rook, .queen] ∧ pr = some k) ∧
      (t.rank ≠ 7 → pr = none)) :
    ⟨s, t, pr⟩ ∈ (if t.rank == Color.last .white then
        ([Kind.knight, .bishop, .rook, .queen].map fun k => (⟨s, t, some k⟩ : Move)) else [⟨s, t, none⟩]) := by
  by_cases h7 : t.rank = 7
  · obtain ⟨k, hk, rfl⟩ := hpr.1 h7
    rw [if_pos (beq_iff_eq.mpr (show t.rank = Color.last .white from h7))]
    exact List.mem_map.mpr ⟨k, hk, rfl⟩
  · obtain rfl := hpr.2 h7
    rw [if_neg (show ¬((t.rank == Color.last .white) = true) from fun h => h7 (beq_iff_eq.mp h))]
    exact List.mem_singleton_self _

theorem pawnMoves_mk_push (p : Pos) (s t : Sq) (pr : Option Kind)
    (hoff : off s 0 1 = some t) (hempty : empty p.board t = true)
    (hpr : (t.rank = 7 → ∃ k, k ∈ [Kind.knight, .bishop, .rook, .queen] ∧ pr = some k) ∧
      (t.rank ≠ 7 → pr = none)) :
    ⟨s, t, pr⟩ ∈ pawnMoves p s .white := by
  refine List.mem_append_left _ ?_
  rw [List.mem_flatMap]
  refine ⟨t, ?_, pawnMoves_mk_aux p s t pr hpr⟩
  refine List.mem_append_left _ ?_
  have hone : (Option.filter (empty p.board) (off s 0 Color.white.fwd)).toList = [t] := by
    rw [show Color.white.fwd = (1 : Int) from rfl, hoff, Option.filter_some, if_pos hempty]
    rfl
  rw [hone]
  exact List.mem_singleton_self _

theorem pawnMoves_mk_double (p : Pos) (s tu t3 : Sq)
    (hsr : s.rank = 1) (hoff1 : off s 0 1 = some tu) (hem1 : empty p.board tu = true)
    (hoff2 : off s 0 2 = some t3) (hem3 : empty p.board t3 = true) :
    ⟨s, t3, none⟩ ∈ pawnMoves p s .white := by
  refine List.mem_append_right _ ?_
  have h1 : (Option.filter (empty p.board) (off s 0 Color.white.fwd)) = some tu := by
    rw [show Color.white.fwd = (1 : Int) from rfl, hoff1, Option.filter_some, if_pos hem1]
  have h2 : Option.filter (empty p.board) (off s 0 (2 * Color.white.fwd)) = some t3 := by
    rw [show Color.white.fwd = (1 : Int) from rfl]
    rw [show (2 : Int) * 1 = 2 from rfl, hoff2, Option.filter_some, if_pos hem3]
  have ht2 : (if (s.rank == Color.pawnHome .white &&
        (Option.filter (empty p.board) (off s 0 Color.white.fwd)).isSome : Bool)
        then Option.filter (empty p.board) (off s 0 (2 * Color.white.fwd)) else none) = some t3 := by
    rw [show Color.white.pawnHome = 1 from rfl, show (s.rank == 1) = true from beq_iff_eq.mpr hsr, h1,
      show (Option.isSome (some tu) : Bool) = true from rfl,
      show ((true : Bool) && true) = true from rfl, if_pos (rfl : (true : Bool) = true)]
    exact h2
  rw [ht2]
  exact List.mem_map.mpr ⟨t3, List.mem_singleton_self _, rfl⟩

theorem pawnMoves_mk_cap (p : Pos) (s t : Sq) (df : Int) (hdf : df = -1 ∨ df = 1) (pr : Option Kind)
    (hoff : off s df 1 = some t)
    (hcond : (foe p.board .white t || epCap p .white t) = true)
    (hpr : (t.rank = 7 → ∃ k, k ∈ [Kind.knight, .bishop, .rook, .queen] ∧ pr = some k) ∧
      (t.rank ≠ 7 → pr = none)) :
    ⟨s, t, pr⟩ ∈ pawnMoves p s .white := by
  refine List.mem_append_left _ ?_
  rw [List.mem_flatMap]
  refine ⟨t, ?_, pawnMoves_mk_aux p s t pr hpr⟩
  refine List.mem_append_right _ ?_
  rw [List.mem_filter]
  refine ⟨?_, hcond⟩
  show t ∈ List.filterMap (fun (d : Int × Int) => off s d.1 d.2) [(1, Color.white.fwd), (-1, Color.white.fwd)]
  show t ∈ List.filterMap (fun (d : Int × Int) => off s d.1 d.2) [(1, (1 : Int)), (-1, 1)]
  rcases hdf with rfl | rfl
  · exact List.mem_filterMap.mpr ⟨(-1, 1), by decide, hoff⟩
  · exact List.mem_filterMap.mpr ⟨(1, 1), by decide, hoff⟩

theorem mkPawn_unfold (q t : Nat) (ps : Ex) (m : Cand) (hm : m ∈ c.mkPawn q t ps) :
    ((fr t).2 = 7 ∧ ∃ k w, 1 ≤ k ∧ k ≤ 4 ∧ m = c.mkMove q t (some k) 0 ps none w) ∨
      ((fr t).2 ≠ 7 ∧ m = c.mkMove q t none 0 ps none 1) := by
  simp only [Cfg.mkPawn] at hm
  split at hm
  · next h7 =>
    simp only [List.mem_map] at hm
    obtain ⟨⟨T, w⟩, hTw, rfl⟩ := hm
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hTw
    rcases hTw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl ⟨beq_iff_eq.mp h7, 1, 4, by decide, by decide, rfl⟩
    · exact .inl ⟨beq_iff_eq.mp h7, 2, 0, by decide, by decide, rfl⟩
    · exact .inl ⟨beq_iff_eq.mp h7, 3, 0, by decide, by decide, rfl⟩
    · exact .inl ⟨beq_iff_eq.mp h7, 4, 0, by decide, by decide, rfl⟩
  · next h7 =>
    exact .inr ⟨fun e => h7 (beq_iff_eq.mpr e), List.mem_singleton.mp hm⟩

theorem piece_pseudo (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (q : Nat) (hq : q ∈ c.squares)
    (m : Cand) (hm : m ∈ c.pieceCands q) :
    m.pseudo.eval A = true ↔ (m.mv ∈ pseudo p ∧ p.board (toSq q) = some ⟨.white, kindOf m.T⟩) := by
  have hturn : p.turn = .white := hf.2.1
  obtain ⟨hq64, -⟩ := List.mem_filter.mp hq
  replace hq64 : q < 64 := List.mem_range.mp hq64
  simp only [Cfg.pieceCands, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨T, hT, t, ht, rfl⟩ := hm
  have ht64 : t < 64 := mem_targets_lt ht
  have ht' : t ∈ List.filter (fun t => !c.isK t) (if T == 1 then knightL q
      else (if T == 3 then orth else if T == 2 then diag else orth ++ diag).flatMap (rayL q)) := ht
  obtain ⟨hout, -⟩ := List.mem_filter.mp ht'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · have hkl : t ∈ knightL q := hout
    show (Ex.and [c.p q 1, Ex.not (c.wocc t)]).eval A = true ↔
      (⟨toSq q, toSq t, none⟩ ∈ pseudo p ∧ p.board (toSq q) = some ⟨.white, .knight⟩)
    constructor
    · intro hv
      rw [eval_and2, Bool.and_eq_true] at hv
      obtain ⟨hev1, hnot⟩ := hv
      rw [eval_p hf hg hl q 1 hq64 (by decide), symOf_decode _ 1 (by decide)] at hev1
      have hbq : p.board (toSq q) = some ⟨.white, .knight⟩ := of_decide_eq_true hev1
      have hany : (p.board (toSq t)).any (fun a => (a.color == .white : Bool)) = false := by
        have h2 := eval_wocc hf hg hl t ht64
        rw [Ex.eval] at hnot
        rw [h2] at hnot
        cases hX : (p.board (toSq t)).any (fun a => (a.color == .white : Bool)) with
        | false => rfl
        | true => rw [hX] at hnot; exact absurd hnot (by decide)
      have hatt : toSq t ∈ attacks p.board (toSq q) ⟨.white, .knight⟩ :=
        (mem_attacks_knight p.board (toSq q) (toSq t) .white).mpr (by
          rw [toSq_val_of_lt t ht64, toSq_val_of_lt q hq64]
          exact hkl)
      exact ⟨mem_pseudo_of p (toSq q) ⟨.white, .knight⟩ ⟨toSq q, toSq t, none⟩ hbq hturn.symm
        (mem_pieceMoves_of_attacks p (toSq q) ⟨.white, .knight⟩ (by decide) (toSq t) hatt hany), hbq⟩
    · rintro ⟨hmem, hbq⟩
      rw [eval_and2, Bool.and_eq_true]
      rcases pseudo_cases hmem with ⟨s', q', hbs, hcol, hpm⟩ | hcm
      · have hsrc := move_src_of_pieceMoves hpm
        rw [show (⟨toSq q, toSq t, none⟩ : Move).src = toSq q from rfl] at hsrc
        subst hsrc
        rw [hbq] at hbs
        obtain rfl := Option.some.inj hbs
        rcases pieceMoves_cases hpm with ⟨hpp, -⟩ | ⟨-, -, -, hdt⟩
        · exact absurd hpp (by decide)
        · obtain ⟨-, hfr⟩ := List.mem_filter.mp hdt
          refine ⟨?_, ?_⟩
          · rw [eval_p hf hg hl q 1 hq64 (by decide), symOf_decode _ 1 (by decide), hbq]
            rfl
          · rw [Ex.eval, eval_wocc hf hg hl t ht64]
            exact hfr
      · obtain ⟨hsrc2, -, hbk2, -, -⟩ := castleMoves_cases hcm
        rw [show (⟨toSq q, toSq t, none⟩ : Move).src = toSq q from rfl] at hsrc2
        rw [← hsrc2, hturn, hbq] at hbk2
        exact absurd (Option.some.inj hbk2) (by decide)
  · have hout' : t ∈ diag.flatMap (rayL q) := hout
    show (Ex.and [c.p q 2, c.clear q t [] [], Ex.not (c.wocc t)]).eval A = true ↔
      (⟨toSq q, toSq t, none⟩ ∈ pseudo p ∧ p.board (toSq q) = some ⟨.white, .bishop⟩)
    constructor
    · intro hv
      rw [eval_and3, Bool.and_eq_true, Bool.and_eq_true] at hv
      obtain ⟨hev2, hclr, hnot⟩ := hv
      rw [eval_p hf hg hl q 2 hq64 (by decide), symOf_decode _ 2 (by decide)] at hev2
      have hbq : p.board (toSq q) = some ⟨.white, .bishop⟩ := of_decide_eq_true hev2
      have hclr' : ∀ u ∈ between q t, p.board (toSq u) = none := by
        rw [eval_clear hf hg hl q t hq64 ht64 [] []] at hclr
        rw [List.all_eq_true] at hclr
        intro u hu
        have h3 := hclr u hu
        simp only [List.not_mem_nil, decide_false, Bool.not_false, Bool.true_and, Bool.false_or] at h3
        exact Option.isNone_iff_eq_none.mp h3
      have hany : (p.board (toSq t)).any (fun a => (a.color == .white : Bool)) = false := by
        have h2 := eval_wocc hf hg hl t ht64
        rw [Ex.eval] at hnot
        rw [h2] at hnot
        cases hX : (p.board (toSq t)).any (fun a => (a.color == .white : Bool)) with
        | false => rfl
        | true => rw [hX] at hnot; exact absurd hnot (by decide)
      obtain ⟨d, hd, htr⟩ := List.mem_flatMap.mp hout'
      have hdir : direction q t = some d :=
        (mem_rayL_iff q t hq64 ht64 d (List.mem_append.mpr (Or.inr hd))).mp htr
      have hatt : toSq t ∈ attacks p.board (toSq q) ⟨.white, .bishop⟩ :=
        (mem_attacks_slider p.board (toSq q) (toSq t) ⟨.white, .bishop⟩ (Or.inl rfl)).mpr
          ⟨d, by rw [toSq_val_of_lt q hq64, toSq_val_of_lt t ht64]; exact hdir,
            ⟨fun h => absurd h (by decide), fun _ => hd⟩, fun u hu => by
              rw [toSq_val_of_lt q hq64, toSq_val_of_lt t ht64] at hu
              exact hclr' u hu⟩
      exact ⟨mem_pseudo_of p (toSq q) ⟨.white, .bishop⟩ ⟨toSq q, toSq t, none⟩ hbq hturn.symm
        (mem_pieceMoves_of_attacks p (toSq q) ⟨.white, .bishop⟩ (by decide) (toSq t) hatt hany), hbq⟩
    · rintro ⟨hmem, hbq⟩
      rcases pseudo_cases hmem with ⟨s', q', hbs, hcol, hpm⟩ | hcm
      · have hsrc := move_src_of_pieceMoves hpm
        rw [show (⟨toSq q, toSq t, none⟩ : Move).src = toSq q from rfl] at hsrc
        subst hsrc
        rw [hbq] at hbs
        obtain rfl := Option.some.inj hbs
        rcases pieceMoves_cases hpm with ⟨hpp, -⟩ | ⟨-, -, -, hdt⟩
        · exact absurd hpp (by decide)
        · obtain ⟨hatt, hfr⟩ := List.mem_filter.mp hdt
          obtain ⟨d', hdir', -, hbtw'⟩ := (mem_attacks_slider p.board (toSq q) (toSq t)
            ⟨.white, .bishop⟩ (Or.inl rfl)).mp hatt
          rw [toSq_val_of_lt q hq64, toSq_val_of_lt t ht64] at hbtw'
          rw [eval_and3, Bool.and_eq_true, Bool.and_eq_true]
          refine ⟨?_, ?_, ?_⟩
          · rw [eval_p hf hg hl q 2 hq64 (by decide), symOf_decode _ 2 (by decide), hbq]
            rfl
          · rw [eval_clear hf hg hl q t hq64 ht64 [] []]
            rw [List.all_eq_true]
            intro u hu
            have hb2 := hbtw' u hu
            simp only [List.not_mem_nil, decide_false, Bool.false_or, Bool.not_false, Bool.true_and]
            rw [hb2]
            rfl
          · rw [Ex.eval, eval_wocc hf hg hl t ht64]
            exact hfr
      · obtain ⟨hsrc2, -, hbk2, -, -⟩ := castleMoves_cases hcm
        rw [show (⟨toSq q, toSq t, none⟩ : Move).src = toSq q from rfl] at hsrc2
        rw [← hsrc2, hturn, hbq] at hbk2
        exact absurd (Option.some.inj hbk2) (by decide)
  · have hout' : t ∈ orth.flatMap (rayL q) := hout
    show (Ex.and [c.p q 3, c.clear q t [] [], Ex.not (c.wocc t)]).eval A = true ↔
      (⟨toSq q, toSq t, none⟩ ∈ pseudo p ∧ p.board (toSq q) = some ⟨.white, .rook⟩)
    constructor
    · intro hv
      rw [eval_and3, Bool.and_eq_true, Bool.and_eq_true] at hv
      obtain ⟨hev3, hclr, hnot⟩ := hv
      rw [eval_p hf hg hl q 3 hq64 (by decide), symOf_decode _ 3 (by decide)] at hev3
      have hbq : p.board (toSq q) = some ⟨.white, .rook⟩ := of_decide_eq_true hev3
      have hclr' : ∀ u ∈ between q t, p.board (toSq u) = none := by
        rw [eval_clear hf hg hl q t hq64 ht64 [] []] at hclr
        rw [List.all_eq_true] at hclr
        intro u hu
        have h3 := hclr u hu
        simp only [List.not_mem_nil, decide_false, Bool.not_false, Bool.true_and, Bool.false_or] at h3
        exact Option.isNone_iff_eq_none.mp h3
      have hany : (p.board (toSq t)).any (fun a => (a.color == .white : Bool)) = false := by
        have h2 := eval_wocc hf hg hl t ht64
        rw [Ex.eval] at hnot
        rw [h2] at hnot
        cases hX : (p.board (toSq t)).any (fun a => (a.color == .white : Bool)) with
        | false => rfl
        | true => rw [hX] at hnot; exact absurd hnot (by decide)
      obtain ⟨d, hd, htr⟩ := List.mem_flatMap.mp hout'
      have hdir : direction q t = some d :=
        (mem_rayL_iff q t hq64 ht64 d (List.mem_append.mpr (Or.inl hd))).mp htr
      have hatt : toSq t ∈ attacks p.board (toSq q) ⟨.white, .rook⟩ :=
        (mem_attacks_slider p.board (toSq q) (toSq t) ⟨.white, .rook⟩ (Or.inr (Or.inl rfl))).mpr
          ⟨d, by rw [toSq_val_of_lt q hq64, toSq_val_of_lt t ht64]; exact hdir,
            ⟨fun _ => hd, fun h => absurd h (by decide)⟩, fun u hu => by
              rw [toSq_val_of_lt q hq64, toSq_val_of_lt t ht64] at hu
              exact hclr' u hu⟩
      exact ⟨mem_pseudo_of p (toSq q) ⟨.white, .rook⟩ ⟨toSq q, toSq t, none⟩ hbq hturn.symm
        (mem_pieceMoves_of_attacks p (toSq q) ⟨.white, .rook⟩ (by decide) (toSq t) hatt hany), hbq⟩
    · rintro ⟨hmem, hbq⟩
      rcases pseudo_cases hmem with ⟨s', q', hbs, hcol, hpm⟩ | hcm
      · have hsrc := move_src_of_pieceMoves hpm
        rw [show (⟨toSq q, toSq t, none⟩ : Move).src = toSq q from rfl] at hsrc
        subst hsrc
        rw [hbq] at hbs
        obtain rfl := Option.some.inj hbs
        rcases pieceMoves_cases hpm with ⟨hpp, -⟩ | ⟨-, -, -, hdt⟩
        · exact absurd hpp (by decide)
        · obtain ⟨hatt, hfr⟩ := List.mem_filter.mp hdt
          obtain ⟨d', hdir', -, hbtw'⟩ := (mem_attacks_slider p.board (toSq q) (toSq t)
            ⟨.white, .rook⟩ (Or.inr (Or.inl rfl))).mp hatt
          rw [toSq_val_of_lt q hq64, toSq_val_of_lt t ht64] at hbtw'
          rw [eval_and3, Bool.and_eq_true, Bool.and_eq_true]
          refine ⟨?_, ?_, ?_⟩
          · rw [eval_p hf hg hl q 3 hq64 (by decide), symOf_decode _ 3 (by decide), hbq]
            rfl
          · rw [eval_clear hf hg hl q t hq64 ht64 [] []]
            rw [List.all_eq_true]
            intro u hu
            have hb2 := hbtw' u hu
            simp only [List.not_mem_nil, decide_false, Bool.false_or, Bool.not_false, Bool.true_and]
            rw [hb2]
            rfl
          · rw [Ex.eval, eval_wocc hf hg hl t ht64]
            exact hfr
      · obtain ⟨hsrc2, -, hbk2, -, -⟩ := castleMoves_cases hcm
        rw [show (⟨toSq q, toSq t, none⟩ : Move).src = toSq q from rfl] at hsrc2
        rw [← hsrc2, hturn, hbq] at hbk2
        exact absurd (Option.some.inj hbk2) (by decide)
  · have hout' : t ∈ (orth ++ diag).flatMap (rayL q) := hout
    show (Ex.and [c.p q 4, c.clear q t [] [], Ex.not (c.wocc t)]).eval A = true ↔
      (⟨toSq q, toSq t, none⟩ ∈ pseudo p ∧ p.board (toSq q) = some ⟨.white, .queen⟩)
    constructor
    · intro hv
      rw [eval_and3, Bool.and_eq_true, Bool.and_eq_true] at hv
      obtain ⟨hev4, hclr, hnot⟩ := hv
      rw [eval_p hf hg hl q 4 hq64 (by decide), symOf_decode _ 4 (by decide)] at hev4
      have hbq : p.board (toSq q) = some ⟨.white, .queen⟩ := of_decide_eq_true hev4
      have hclr' : ∀ u ∈ between q t, p.board (toSq u) = none := by
        rw [eval_clear hf hg hl q t hq64 ht64 [] []] at hclr
        rw [List.all_eq_true] at hclr
        intro u hu
        have h3 := hclr u hu
        simp only [List.not_mem_nil, decide_false, Bool.not_false, Bool.true_and, Bool.false_or] at h3
        exact Option.isNone_iff_eq_none.mp h3
      have hany : (p.board (toSq t)).any (fun a => (a.color == .white : Bool)) = false := by
        have h2 := eval_wocc hf hg hl t ht64
        rw [Ex.eval] at hnot
        rw [h2] at hnot
        cases hX : (p.board (toSq t)).any (fun a => (a.color == .white : Bool)) with
        | false => rfl
        | true => rw [hX] at hnot; exact absurd hnot (by decide)
      obtain ⟨d, hd, htr⟩ := List.mem_flatMap.mp hout'
      have hdir : direction q t = some d :=
        (mem_rayL_iff q t hq64 ht64 d hd).mp htr
      have hatt : toSq t ∈ attacks p.board (toSq q) ⟨.white, .queen⟩ :=
        (mem_attacks_slider p.board (toSq q) (toSq t) ⟨.white, .queen⟩ (Or.inr (Or.inr rfl))).mpr
          ⟨d, by rw [toSq_val_of_lt q hq64, toSq_val_of_lt t ht64]; exact hdir,
            ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, fun u hu => by
              rw [toSq_val_of_lt q hq64, toSq_val_of_lt t ht64] at hu
              exact hclr' u hu⟩
      exact ⟨mem_pseudo_of p (toSq q) ⟨.white, .queen⟩ ⟨toSq q, toSq t, none⟩ hbq hturn.symm
        (mem_pieceMoves_of_attacks p (toSq q) ⟨.white, .queen⟩ (by decide) (toSq t) hatt hany), hbq⟩
    · rintro ⟨hmem, hbq⟩
      rcases pseudo_cases hmem with ⟨s', q', hbs, hcol, hpm⟩ | hcm
      · have hsrc := move_src_of_pieceMoves hpm
        rw [show (⟨toSq q, toSq t, none⟩ : Move).src = toSq q from rfl] at hsrc
        subst hsrc
        rw [hbq] at hbs
        obtain rfl := Option.some.inj hbs
        rcases pieceMoves_cases hpm with ⟨hpp, -⟩ | ⟨-, -, -, hdt⟩
        · exact absurd hpp (by decide)
        · obtain ⟨hatt, hfr⟩ := List.mem_filter.mp hdt
          obtain ⟨d', hdir', -, hbtw'⟩ := (mem_attacks_slider p.board (toSq q) (toSq t)
            ⟨.white, .queen⟩ (Or.inr (Or.inr rfl))).mp hatt
          rw [toSq_val_of_lt q hq64, toSq_val_of_lt t ht64] at hbtw'
          rw [eval_and3, Bool.and_eq_true, Bool.and_eq_true]
          refine ⟨?_, ?_, ?_⟩
          · rw [eval_p hf hg hl q 4 hq64 (by decide), symOf_decode _ 4 (by decide), hbq]
            rfl
          · rw [eval_clear hf hg hl q t hq64 ht64 [] []]
            rw [List.all_eq_true]
            intro u hu
            have hb2 := hbtw' u hu
            simp only [List.not_mem_nil, decide_false, Bool.false_or, Bool.not_false, Bool.true_and]
            rw [hb2]
            rfl
          · rw [Ex.eval, eval_wocc hf hg hl t ht64]
            exact hfr
      · obtain ⟨hsrc2, -, hbk2, -, -⟩ := castleMoves_cases hcm
        rw [show (⟨toSq q, toSq t, none⟩ : Move).src = toSq q from rfl] at hsrc2
        rw [← hsrc2, hturn, hbq] at hbk2
        exact absurd (Option.some.inj hbk2) (by decide)

theorem pawn_pseudo (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hr : RightsOk c s r)
    (q : Nat) (hq : q ∈ c.squares) (m : Cand) (hm : m ∈ c.pawnCands r q) (h : m.pseudo.eval A = true) :
    m.mv ∈ pseudo p ∧ m.KindOk p ∧ p.board (toSq q) = some ⟨.white, .pawn⟩ := by
  have hturn : p.turn = .white := hf.2.1
  obtain ⟨hq64, -⟩ := List.mem_filter.mp hq
  replace hq64 : q < 64 := List.mem_range.mp hq64
  obtain ⟨hf0, hf8, hr0, hr8⟩ := fr_bounds q hq64
  have hbpq : (symOf (p.board (toSq q)) == 0) = decide (p.board (toSq q) = some ⟨.white, .pawn⟩) :=
    symOf_decode _ 0 (by decide)
  simp only [Cfg.pawnCands] at hm
  generalize ht1' : (sqo (fr q).1 ((fr q).2 + 1)).getD 0 = t1 at hm
  generalize ht3' : (sqo (fr q).1 3).getD 0 = t3 at hm
  have ht1 : t1 = (sqo (fr q).1 ((fr q).2 + 1)).getD 0 := ht1'.symm
  have ht3 : t3 = (sqo (fr q).1 3).getD 0 := ht3'.symm
  split at hm
  · simp at hm
  · rename_i h07
    have hrk07 : (fr q).2 ≠ 0 ∧ (fr q).2 ≠ 7 := by
      refine ⟨fun e => ?_, fun e => ?_⟩
      · apply h07; rw [e]; rfl
      · apply h07; rw [e]; rfl
    have hsqo1 : sqo (fr q).1 ((fr q).2 + 1) = some (((fr q).1 + 8 * ((fr q).2 + 1)).toNat) :=
      sqo_some hf0 hf8 (by omega) (by omega)
    have ht1v : t1 = ((fr q).1 + 8 * ((fr q).2 + 1)).toNat := by rw [ht1, hsqo1, Option.getD_some]
    have ht164 : t1 < 64 := by omega
    have hoff1 : off (toSq q) 0 1 = some (toSq t1) := off_of_sqo q hq64 0 1 (by rw [Int.add_zero, hsqo1, ht1v])
    have hff1 : (toSq q).file = (toSq t1).file := by
      rw [file_toSq hq64, file_toSq ht164]
      rw [ht1v]
      have hfr1 : (fr q).1 = ((q % 8 : Nat) : Int) := rfl
      omega
    rcases List.mem_append.mp hm with hmp | hmc
    · split at hmp
      · simp at hmp
      · rcases List.mem_append.mp hmp with hmp1 | hmp2
        · obtain ⟨h7, kk, w, hk1, hk4, mdef⟩ | ⟨h7, mdef⟩ :=
            mkPawn_unfold q t1 (.and [c.p q 0, c.empty t1]) m hmp1
          · subst mdef
            change (Ex.and [c.p q 0, c.empty t1]).eval A = true at h
            rw [eval_and2, Bool.and_eq_true] at h
            obtain ⟨hev0, hem1⟩ := h
            rw [eval_p hf hg hl q 0 hq64 (by decide), hbpq] at hev0
            have hpq : p.board (toSq q) = some ⟨.white, .pawn⟩ := of_decide_eq_true hev0
            rw [eval_empty hf hg hl t1 ht164] at hem1
            have hem1' : empty p.board (toSq t1) = true := by rw [empty]; exact hem1
            have h7r : (toSq t1).rank = 7 := by
              have := fr_snd ht164
              omega
            refine ⟨?_, ?_, hpq⟩
            · exact mem_pseudo_of p (toSq q) ⟨.white, .pawn⟩ ⟨toSq q, toSq t1, some (kindOf kk)⟩ hpq
                hturn.symm
                (pawnMoves_mk_push p (toSq q) (toSq t1) (some (kindOf kk)) hoff1 hem1'
                  ⟨fun _ => ⟨kindOf kk, kindOf_promos kk hk1 hk4, rfl⟩, fun hne => absurd h7r hne⟩)
            · apply kindOk_of_none
              · rfl
              · exact isCastle_false_of_kind p ⟨toSq q, toSq t1, some (kindOf kk)⟩ (k := .pawn)
                  (by decide) hpq
              · exact isEp_false_of_same_file p ⟨toSq q, toSq t1, some (kindOf kk)⟩ hpq hff1
          · subst mdef
            change (Ex.and [c.p q 0, c.empty t1]).eval A = true at h
            rw [eval_and2, Bool.and_eq_true] at h
            obtain ⟨hev0, hem1⟩ := h
            rw [eval_p hf hg hl q 0 hq64 (by decide), hbpq] at hev0
            have hpq : p.board (toSq q) = some ⟨.white, .pawn⟩ := of_decide_eq_true hev0
            rw [eval_empty hf hg hl t1 ht164] at hem1
            have hem1' : empty p.board (toSq t1) = true := by rw [empty]; exact hem1
            have h7n : (toSq t1).rank ≠ 7 := by
              intro hh
              apply h7
              rw [fr_snd ht164, hh]
              rfl
            refine ⟨?_, ?_, hpq⟩
            · exact mem_pseudo_of p (toSq q) ⟨.white, .pawn⟩ ⟨toSq q, toSq t1, none⟩ hpq hturn.symm
                (pawnMoves_mk_push p (toSq q) (toSq t1) none hoff1 hem1'
                  ⟨fun h7' => absurd h7' h7n, fun _ => rfl⟩)
            · apply kindOk_of_none
              · rfl
              · exact isCastle_false_of_kind p ⟨toSq q, toSq t1, none⟩ (k := .pawn) (by decide) hpq
              · exact isEp_false_of_same_file p ⟨toSq q, toSq t1, none⟩ hpq hff1
        · split at hmp2
          · rename_i hgd
            rw [Bool.and_eq_true] at hgd
            have hR1 : (fr q).2 = 1 := beq_iff_eq.mp hgd.1
            have hsqo3 : sqo (fr q).1 3 = some (((fr q).1 + 8 * 3).toNat) :=
              sqo_some hf0 hf8 (by decide) (by decide)
            have ht3v : t3 = ((fr q).1 + 8 * (3 : Int)).toNat := by rw [ht3, hsqo3, Option.getD_some]
            have ht364 : t3 < 64 := by omega
            have ht3rank : (toSq t3).rank = 3 := by
              rw [rank_toSq ht364]
              have hfr1 : (fr q).1 = ((q % 8 : Nat) : Int) := rfl
              omega
            obtain ⟨h7, kk, w, hk1, hk4, mdef⟩ | ⟨h7, mdef⟩ :=
              mkPawn_unfold q t3 (.and [c.p q 0, c.empty t1, c.empty t3]) m hmp2
            · exfalso
              have hfs := fr_snd ht364
              rw [ht3rank] at hfs
              omega
            · subst mdef
              change (Ex.and [c.p q 0, c.empty t1, c.empty t3]).eval A = true at h
              rw [eval_and3, Bool.and_eq_true, Bool.and_eq_true] at h
              obtain ⟨hev0, hem1, hem3⟩ := h
              rw [eval_p hf hg hl q 0 hq64 (by decide), hbpq] at hev0
              have hpq : p.board (toSq q) = some ⟨.white, .pawn⟩ := of_decide_eq_true hev0
              rw [eval_empty hf hg hl t1 ht164] at hem1
              rw [eval_empty hf hg hl t3 ht364] at hem3
              have hem1' : empty p.board (toSq t1) = true := by rw [empty]; exact hem1
              have hem3' : empty p.board (toSq t3) = true := by rw [empty]; exact hem3
              have hsr : (toSq q).rank = 1 := by
                have := fr_snd hq64
                omega
              have hoff2 : off (toSq q) 0 2 = some (toSq t3) :=
                off_of_sqo q hq64 0 2 (by rw [Int.add_zero, hR1, show ((1 : Int) + 2) = 3 from rfl, hsqo3, ht3v])
              have hff3 : (toSq q).file = (toSq t3).file := by
                rw [file_toSq hq64, file_toSq ht364, ht3v]
                have hfr1 : (fr q).1 = ((q % 8 : Nat) : Int) := rfl
                omega
              refine ⟨?_, ?_, hpq⟩
              · exact mem_pseudo_of p (toSq q) ⟨.white, .pawn⟩ ⟨toSq q, toSq t3, none⟩ hpq hturn.symm
                  (pawnMoves_mk_double p (toSq q) (toSq t1) (toSq t3) hsr hoff1 hem1' hoff2 hem3')
              · apply kindOk_of_none
                · rfl
                · exact isCastle_false_of_kind p ⟨toSq q, toSq t3, none⟩ (k := .pawn) (by decide) hpq
                · exact isEp_false_of_same_file p ⟨toSq q, toSq t3, none⟩ hpq hff3
          · simp at hmp2
    · obtain ⟨df, hdf, hmdf⟩ := List.mem_flatMap.mp hmc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hdf
      split at hmdf
      · simp at hmdf
      · rename_i t' hsq
        obtain ⟨hF0, hF8, hr0', hr8', ht'v⟩ := sqo_bounds hsq
        have ht'64 : t' < 64 := sqo_lt hsq
        have hoff : off (toSq q) df 1 = some (toSq t') := off_of_sqo q hq64 df 1 hsq
        split at hmdf
        · simp at hmdf
        · rcases List.mem_append.mp hmdf with hb1 | hb2
          · obtain ⟨h7, kk, w, hk1, hk4, mdef⟩ | ⟨h7, mdef⟩ :=
              mkPawn_unfold q t' (.and [c.p q 0, c.has t' symB]) m hb1
            · subst mdef
              change (Ex.and [c.p q 0, c.has t' symB]).eval A = true at h
              rw [eval_and2, Bool.and_eq_true] at h
              obtain ⟨hev0, hhas⟩ := h
              rw [eval_p hf hg hl q 0 hq64 (by decide), hbpq] at hev0
              have hpq : p.board (toSq q) = some ⟨.white, .pawn⟩ := of_decide_eq_true hev0
              rw [eval_has hf hg hl t' ht'64 symB (by intro k hk; simp [symB] at hk; omega)] at hhas
              obtain ⟨kd, hb'⟩ := symOf_mem_symB (List.contains_iff_mem.mp hhas)
              have hfoe1 : foe p.board .white (toSq t') = true := by
                rw [foe, hb']
                rfl
              have h7r : (toSq t').rank = 7 := by
                have := fr_snd ht'64
                omega
              refine ⟨?_, ?_, hpq⟩
              · exact mem_pseudo_of p (toSq q) ⟨.white, .pawn⟩ ⟨toSq q, toSq t', some (kindOf kk)⟩ hpq
                  hturn.symm
                  (pawnMoves_mk_cap p (toSq q) (toSq t') df hdf (some (kindOf kk)) hoff
                    (by rw [hfoe1, Bool.true_or])
                    ⟨fun _ => ⟨kindOf kk, kindOf_promos kk hk1 hk4, rfl⟩, fun hne => absurd h7r hne⟩)
              · apply kindOk_of_none
                · rfl
                · exact isCastle_false_of_kind p ⟨toSq q, toSq t', some (kindOf kk)⟩ (k := .pawn)
                    (by decide) hpq
                · exact isEp_false_of_dst_some p ⟨toSq q, toSq t', some (kindOf kk)⟩ hb'
            · subst mdef
              change (Ex.and [c.p q 0, c.has t' symB]).eval A = true at h
              rw [eval_and2, Bool.and_eq_true] at h
              obtain ⟨hev0, hhas⟩ := h
              rw [eval_p hf hg hl q 0 hq64 (by decide), hbpq] at hev0
              have hpq : p.board (toSq q) = some ⟨.white, .pawn⟩ := of_decide_eq_true hev0
              rw [eval_has hf hg hl t' ht'64 symB (by intro k hk; simp [symB] at hk; omega)] at hhas
              obtain ⟨kd, hb'⟩ := symOf_mem_symB (List.contains_iff_mem.mp hhas)
              have hfoe1 : foe p.board .white (toSq t') = true := by
                rw [foe, hb']
                rfl
              have h7n : (toSq t').rank ≠ 7 := by
                intro hh
                apply h7
                rw [fr_snd ht'64, hh]
                rfl
              refine ⟨?_, ?_, hpq⟩
              · exact mem_pseudo_of p (toSq q) ⟨.white, .pawn⟩ ⟨toSq q, toSq t', none⟩ hpq hturn.symm
                  (pawnMoves_mk_cap p (toSq q) (toSq t') df hdf none hoff
                    (by rw [hfoe1, Bool.true_or])
                    ⟨fun h7' => absurd h7' h7n, fun _ => rfl⟩)
              · apply kindOk_of_none
                · rfl
                · exact isCastle_false_of_kind p ⟨toSq q, toSq t', none⟩ (k := .pawn) (by decide) hpq
                · exact isEp_false_of_dst_some p ⟨toSq q, toSq t', none⟩ hb'
          · split at hb2
            · rename_i v hvμ
              by_cases h4b : ((fr q).2 == 4) = true
              · rw [if_pos h4b] at hvμ
                have hR4 : (fr q).2 = 4 := beq_iff_eq.mp h4b
                have hme : m = c.mkMove q t' none 0 (.and [c.p q 0, .v v]) (sqo ((fr q).1 + df) 4) 1 :=
                  List.mem_singleton.mp hb2
                subst hme
                change (Ex.and [c.p q 0, .v v]).eval A = true at h
                rw [eval_and2, Bool.and_eq_true] at h
                obtain ⟨hev0, hvev⟩ := h
                rw [eval_p hf hg hl q 0 hq64 (by decide), hbpq] at hev0
                have hpq : p.board (toSq q) = some ⟨.white, .pawn⟩ := of_decide_eq_true hev0
                have hmem : (((fr q).1 + df).toNat, v) ∈ r.ep := mem_of_lookup_eq_some r.ep hvμ
                obtain ⟨hFs, hvpos, hd⟩ := hr.1 _ _ hmem
                obtain ⟨hi, hd2⟩ := Array.getElem?_eq_some_iff.mp hd
                have hAv := hg _ hi
                rw [hd2, show v.toNat - 1 + 1 = v.toNat from by omega] at hAv
                have hlv : (Ex.v v).eval A = A v.toNat := by
                  show litVal A v = A v.toNat
                  rw [litVal, if_pos hvpos]
                rw [hlv, hAv] at hvev
                have hep : p.ep = some (toSq (((fr q).1 + df).toNat + 40)) := beq_iff_eq.mp hvev
                have heok : EpOk p (toSq (((fr q).1 + df).toNat + 40)) := hf.1.ep _ hep
                unfold EpOk at heok
                rw [hturn] at heok
                obtain ⟨hr5, hbp, hbn, -⟩ := heok
                have hF8' : ((fr q).1 + df).toNat < 8 := by
                  have : ((fr q).1 + df).toNat = ((fr q).1 + df).toNat := rfl
                  omega
                have ht'F : t' = ((fr q).1 + df).toNat + 40 := by omega
                have hfile0 : (toSq (((fr q).1 + df).toNat + 40)).file = ((fr q).1 + df).toNat := by
                  rw [file_toSq (by omega : ((fr q).1 + df).toNat + 40 < 64)]
                  omega
                have hbpv : p.board (sq ((fr q).1 + df).toNat 4) = some ⟨.black, .pawn⟩ := by
                  have h2 := hbp
                  rw [hfile0] at h2
                  exact h2
                have hbnv : p.board (toSq t') = none := by rw [ht'F]; exact hbn
                have hbt : (p.ep == some (toSq t')) = true := by
                  rw [ht'F, hep]
                  exact beq_self_eq_true _
                have hemv : empty p.board (toSq t') = true := by
                  rw [empty, ht'F, hbn]
                  rfl
                have hoffv : off (toSq t') 0 (-1) = some (sq ((fr q).1 + df).toNat 4) := by
                  rw [off_eq_some]
                  refine ⟨?_, ?_⟩
                  · rw [sq_file _ _ hF8' (by decide), file_toSq ht'64]
                    omega
                  · rw [sq_rank _ _ hF8' (by decide), rank_toSq ht'64]
                    omega
                have hcap : epCap p .white (toSq t') = true := by
                  rw [epCap, show (-Color.white.fwd) = (-1 : Int) from rfl, hbt, Bool.true_and, hemv,
                    Bool.true_and, hoffv]
                  show ((p.board (sq ((fr q).1 + df).toNat 4)) == some ⟨Color.white.opp, .pawn⟩) = true
                  rw [hbpv]
                  rfl
                have ht'rank : (toSq t').rank = 5 := by
                  rw [rank_toSq ht'64]
                  omega
                have hdfne : df ≠ 0 := by rcases hdf with rfl | rfl <;> decide
                have hfn : (toSq q).file ≠ (toSq t').file := by
                  rw [file_toSq hq64, file_toSq ht'64]
                  have hfr1 : (fr q).1 = ((q % 8 : Nat) : Int) := rfl
                  omega
                refine ⟨?_, ?_, hpq⟩
                · exact mem_pseudo_of p (toSq q) ⟨.white, .pawn⟩ ⟨toSq q, toSq t', none⟩ hpq hturn.symm
                    (pawnMoves_mk_cap p (toSq q) (toSq t') df hdf none hoff
                      (by rw [hcap, Bool.or_true])
                      ⟨fun h7' => absurd h7' (by rw [ht'rank]; decide), fun _ => rfl⟩)
                · apply kindOk_ep
                  · have hsqo4 : sqo ((fr q).1 + df) 4 = some (((fr q).1 + df) + 8 * 4).toNat :=
                      sqo_some hF0 hF8 (by decide) (by decide)
                    show sqo ((fr q).1 + df) 4 = some _
                    exact hsqo4
                  · exact isCastle_false_of_kind p ⟨toSq q, toSq t', none⟩ (k := .pawn) (by decide) hpq
                  · show isEp p ⟨toSq q, toSq t', none⟩ = true
                    rw [isEp, hpq, Option.any_some]
                    rw [show ((Kind.pawn : Kind) == .pawn) = true from rfl, Bool.true_and]
                    rw [show ((toSq q).file != (toSq t').file) = true from bne_iff_ne.mpr hfn,
                      Bool.true_and]
                    exact hemv
                  · have hfv : (toSq t').file = ((fr q).1 + df).toNat := by
                      rw [file_toSq ht'64]; omega
                    have hev4 : (toSq q).rank = 4 := by
                      have := fr_snd hq64; omega
                    have hval : (epVictim (⟨toSq q, toSq t', none⟩ : Move)).val =
                        (32 + ((fr q).1 + df).toNat) := by
                      show (sq ((toSq t').file) ((toSq q).rank)).val = _
                      rw [sq_val, sq_rank _ _ (file_lt _) (rank_lt _), sq_file _ _ (file_lt _) (rank_lt _),
                        hfv, hev4]
                    rw [show (c.mkMove q t' none 0 (.and [c.p q 0, .v v]) (sqo ((fr q).1 + df) 4) 1).mv =
                      (⟨toSq q, toSq t', none⟩ : Move) from rfl, hval]
                    omega
              · rw [if_neg h4b] at hvμ
                exact absurd hvμ (by simp)
            · simp at hb2

theorem piece_kind (hf : Fits c p) (q : Nat) (hq : q ∈ c.squares) (m : Cand) (hm : m ∈ c.pieceCands q)
    (h : m.mv ∈ pseudo p) (hp : p.board (toSq q) = some ⟨.white, kindOf m.T⟩) : m.KindOk p := by
  simp only [Cfg.pieceCands, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨T, hT, t, ht, rfl⟩ := hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact kindOk_of_none p _ rfl
      (isCastle_false_of_kind p ⟨toSq q, toSq t, none⟩ (k := .knight) (by decide) hp)
      (isEp_false_of_kind p ⟨toSq q, toSq t, none⟩ (k := .knight) (by decide) hp)
  · exact kindOk_of_none p _ rfl
      (isCastle_false_of_kind p ⟨toSq q, toSq t, none⟩ (k := .bishop) (by decide) hp)
      (isEp_false_of_kind p ⟨toSq q, toSq t, none⟩ (k := .bishop) (by decide) hp)
  · exact kindOk_of_none p _ rfl
      (isCastle_false_of_kind p ⟨toSq q, toSq t, none⟩ (k := .rook) (by decide) hp)
      (isEp_false_of_kind p ⟨toSq q, toSq t, none⟩ (k := .rook) (by decide) hp)
  · exact kindOk_of_none p _ rfl
      (isCastle_false_of_kind p ⟨toSq q, toSq t, none⟩ (k := .queen) (by decide) hp)
      (isEp_false_of_kind p ⟨toSq q, toSq t, none⟩ (k := .queen) (by decide) hp)

theorem cheb_symm (a b : Nat) : cheb a b = cheb b a := by
  unfold cheb
  have h1 : (fr b).1 - (fr a).1 = -((fr a).1 - (fr b).1) := by omega
  have h2 : (fr b).2 - (fr a).2 = -((fr a).2 - (fr b).2) := by omega
  rw [h1, h2, Int.natAbs_neg, Int.natAbs_neg]

theorem inCheck_eq_of_uniq {b : Board} {c : Color} {s : Sq}
    (hs : b s = some ⟨c, .king⟩) (hu : ∀ t : Sq, b t = some ⟨c, .king⟩ → t = s) :
    (allSq.any fun t => b t == some ⟨c, .king⟩ && attacked b t c.opp) = attacked b s c.opp := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    obtain ⟨t, -, ht⟩ := List.any_eq_true.mp h
    rw [Bool.and_eq_true] at ht
    have hts : t = s := hu t (beq_iff_eq.mp ht.1)
    subst hts
    exact ht.2
  · intro h
    exact List.any_eq_true.mpr ⟨s, List.mem_finRange s, by
      rw [Bool.and_eq_true]; exact ⟨beq_iff_eq.mpr hs, h⟩⟩

theorem mv_src_ne_dst {p : Pos} {m : Move} (h : m ∈ pseudo p) : m.src ≠ m.dst := by
  obtain ⟨pw, hsrc, hcol⟩ := pseudo_src h
  intro e
  have h2 : p.board m.dst = some pw := e ▸ hsrc
  exact absurd hcol (pseudo_dst h pw h2)

theorem mem_singleton_ne {a b : Nat} (h : a ≠ b) : ¬ a ∈ [b] := by
  simp only [List.mem_singleton]
  exact h

theorem fits_cheb_gt_one (hf : Fits c p) : 1 < cheb c.kw c.kb ∧ 1 < cheb c.kb c.kw := by
  have hok := fits_cfgOk hf
  obtain ⟨hkw64, hkb64, -⟩ := hok
  have hkwv : (kingSq p .white).val = c.kw := congrArg Cfg.kw hf.2.2
  have hkbv : (kingSq p .black).val = c.kb := congrArg Cfg.kb hf.2.2
  have hkw2 : toSq c.kw = kingSq p .white :=
    Fin.ext (by rw [toSq_val_of_lt c.kw hkw64]; exact hkwv.symm)
  have hkb2 : toSq c.kb = kingSq p .black :=
    Fin.ext (by rw [toSq_val_of_lt c.kb hkb64]; exact hkbv.symm)
  rw [cheb_symm c.kb c.kw, cheb_toSq _ _ hkw64 hkb64, hkw2, hkb2]
  exact ⟨hf.1.apart, hf.1.apart⟩

theorem toSq_inj_of_lt {a b : Nat} (ha : a < 64) (hb : b < 64) (h : toSq a = toSq b) : a = b := by
  have h1 := toSq_val_of_lt a ha
  have h2 := toSq_val_of_lt b hb
  have h3 := congrArg Fin.val h
  rw [h1, h2] at h3
  exact h3

theorem between_ne_tab : ∀ a ∈ List.range 64, ∀ b ∈ List.range 64, ∀ u ∈ List.range 64,
    (u ∈ between a b → u ≠ a ∧ u ≠ b) := by
  decide +kernel

theorem mem_between_ne {a b u : Nat} (ha : a < 64) (hb : b < 64) (h : u ∈ between a b) :
    u ≠ a ∧ u ≠ b :=
  between_ne_tab a (List.mem_range.mpr ha) b (List.mem_range.mpr hb) u
    (List.mem_range.mpr (between_lt64 h)) h

theorem attExcl_of_dstColor {b' : Board} {s : Sq} {d : Nat} {col : Color}
    (hcol : ∀ pc, b' (toSq d) = some pc → pc.color ≠ col) :
    (∃ t : Sq, t.val ∉ [d] ++ [d] ∧ ∃ pc, b' t = some pc ∧ pc.color = col ∧ s ∈ attacks b' t pc) ↔
      ∃ t pc, b' t = some pc ∧ pc.color = col ∧ s ∈ attacks b' t pc := by
  constructor
  · rintro ⟨t, -, pc, hb, hc, ha⟩
    exact ⟨t, pc, hb, hc, ha⟩
  · rintro ⟨t, pc, hb, hc, ha⟩
    refine ⟨t, ?_, pc, hb, hc, ha⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_self, or_false]
    intro htv
    have htd : t = toSq d := by
      have h1 : toSq t.val = t := toSq_val t
      rw [htv] at h1
      exact h1.symm
    subst htd
    exact absurd hc (hcol pc hb)

theorem attSplit_dst {b' : Board} {s : Sq} {d : Nat} {col : Color}
    {pc0 : Piece} (h0 : b' (toSq d) = some pc0) (hc0 : pc0.color = col) :
    (∃ t pc, b' t = some pc ∧ pc.color = col ∧ s ∈ attacks b' t pc) ↔
      (s ∈ attacks b' (toSq d) pc0) ∨
        ∃ t : Sq, t.val ∉ [d] ++ [d] ∧ ∃ pc, b' t = some pc ∧ pc.color = col ∧ s ∈ attacks b' t pc := by
  constructor
  · rintro ⟨t, pc, hb, hc, ha⟩
    by_cases htd : t = toSq d
    · subst htd
      rw [h0] at hb
      obtain rfl := Option.some.inj hb
      exact Or.inl ha
    · refine Or.inr ⟨t, ?_, pc, hb, hc, ha⟩
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_self, or_false]
      intro htv
      apply htd
      have h1 : toSq t.val = t := toSq_val t
      rw [htv] at h1
      exact h1.symm
  · rintro (h | ⟨t, -, pc, hb, hc, ha⟩)
    · exact ⟨toSq d, pc0, h0, hc0, h⟩
    · exact ⟨t, pc, hb, hc, ha⟩

theorem toSq_eq_val (s : Sq) (q : Nat) (h : q = s.val) : toSq q = s := by
  rw [h]
  exact toSq_val s

theorem king_loc_of_play {p : Pos} {b' : Board} {d : Sq} {R : List Sq} {qm : Piece} {ks : Sq} {col : Color}
    (hbd : b' d = some qm) (hqm : qm ≠ ⟨col, .king⟩)
    (hR : ∀ s : Sq, s ∈ R → b' s = none)
    (hskips : ∀ s : Sq, s ≠ d → s ∉ R → b' s = p.board s)
    (huniq : ∀ s : Sq, p.board s = some ⟨col, .king⟩ → s = ks)
    (hks : p.board ks = some ⟨col, .king⟩) (hksR : ks ∉ R) (hksd : ks ≠ d) :
    ∀ t : Sq, b' t = some ⟨col, .king⟩ ↔ t = ks := by
  intro t
  constructor
  · intro ht
    have htd : t ≠ d := by
      intro e
      subst e
      rw [hbd] at ht
      obtain rfl := Option.some.inj ht
      exact hqm rfl
    have htR : t ∉ R := by
      intro hr
      rw [hR t hr] at ht
      exact absurd ht (by simp)
    rw [hskips t htd htR] at ht
    exact huniq t ht
  · intro ht
    rw [ht, hskips ks hksd hksR]
    exact hks

theorem mk_play_facts (hf : Fits c p) (m : Cand) (hmv : m.mv ∈ pseudo p) (hkind : m.KindOk p)
    (hsrc64 : m.src < 64) (hdst64 : m.dst < 64) (hkwsrc : m.src ≠ c.kw)
    (hpk : ∀ k : Kind, m.mv.promo = some k → k ≠ .king) :
    Agrees p (play p m.mv).board (m.src :: m.ep.toList) [m.dst] [m.dst]
      ∧ (∀ t : Sq, (play p m.mv).board t = some ⟨.black, .king⟩ ↔ t = toSq c.kb)
      ∧ (∀ t : Sq, (play p m.mv).board t = some ⟨.white, .king⟩ ↔ t = toSq c.kw)
      ∧ (∃ pc, (play p m.mv).board (toSq m.dst) = some pc ∧ pc.color = .white)
      ∧ (∀ q ∈ m.src :: m.ep.toList, q ∉ [m.dst])
      ∧ c.kb ∉ (m.src :: m.ep.toList) ++ [m.dst]
      ∧ c.kw ∉ [m.dst]
      ∧ (∀ q ∈ m.src :: m.ep.toList, q < 64) := by
  have hA := hf.1
  have hturn : p.turn = .white := hf.2.1
  have hok := fits_cfgOk hf
  obtain ⟨hkw64, hkb64, -⟩ := hok
  obtain ⟨hwb, hbb, -⟩ := fits_kings hf
  have hkwv : (kingSq p .white).val = c.kw := congrArg Cfg.kw hf.2.2
  have hkbv : (kingSq p .black).val = c.kb := congrArg Cfg.kb hf.2.2
  have hkw2 : toSq c.kw = kingSq p .white :=
    Fin.ext (by rw [toSq_val_of_lt c.kw hkw64]; exact hkwv.symm)
  have hkb2 : toSq c.kb = kingSq p .black :=
    Fin.ext (by rw [toSq_val_of_lt c.kb hkb64]; exact hkbv.symm)
  have hwuniq : ∀ s : Sq, p.board s = some ⟨.white, .king⟩ → s = toSq c.kw :=
    fun s hs => ((kingSq_spec p .white (hA.kings .white)).2 s hs).trans hkw2.symm
  have hbuniq : ∀ s : Sq, p.board s = some ⟨.black, .king⟩ → s = toSq c.kb :=
    fun s hs => ((kingSq_spec p .black (hA.kings .black)).2 s hs).trans hkb2.symm
  obtain ⟨hkC, hkE⟩ := hkind
  obtain ⟨pw, hsrcb0, hsrcw⟩ := pseudo_src hmv
  have hsrcw' : pw.color = .white := hsrcw.trans hturn
  have hsrce : m.mv.src = toSq m.src := rfl
  have hdstE : m.mv.dst = toSq m.dst := rfl
  have hsrcb : p.board (toSq m.src) = some pw := by rw [← hsrce]; exact hsrcb0
  have hsd : m.mv.src ≠ m.mv.dst := mv_src_ne_dst hmv
  have hsd' : m.src ≠ m.dst := fun e => hsd ((hsrce.trans (congrArg toSq e)).trans hdstE.symm)
  have hsrc_ne_kw : toSq m.src ≠ toSq c.kw := fun e => hkwsrc (toSq_inj_of_lt hsrc64 hkw64 e)
  have hsrc_ne_kb : toSq m.src ≠ toSq c.kb := by
    intro e
    have hb' : p.board (toSq c.kb) = some pw := by rw [← e]; exact hsrcb
    rw [hbb] at hb'
    obtain rfl := Option.some.inj hb'
    exact absurd hsrcw' (by decide)
  have hdpoly : p.board m.mv.dst ≠ some ⟨.black, .king⟩ := by
    have h := pseudo_no_king_capture hA hmv
    rwa [hturn] at h
  have hdst_ne_kw : toSq m.dst ≠ toSq c.kw := by
    intro e
    have hb' : p.board (toSq m.dst) = some ⟨.white, .king⟩ := by rw [e]; exact hwb
    have hc := pseudo_dst hmv ⟨.white, .king⟩ (by rw [hdstE]; exact hb')
    exact hc (by rw [hturn])
  have hdst_ne_kb : toSq m.dst ≠ toSq c.kb := by
    intro e
    have hb' : p.board m.mv.dst = some ⟨.black, .king⟩ := by
      rw [hdstE, e]; exact hbb
    exact hdpoly hb'
  have hpwk : pw.kind ≠ .king := by
    intro hk
    cases pw with
    | mk c0 k0 =>
      have hc0 : c0 = .white := hsrcw'
      have hk0 : k0 = .king := hk
      subst hc0
      subst hk0
      exact hsrc_ne_kw (hwuniq (toSq m.src) hsrcb)
  obtain ⟨qm, hqmE, hqmc, hqmk⟩ : ∃ qm : Piece, moved p m.mv = some qm ∧ qm.color = .white ∧
      qm.kind ≠ .king := by
    unfold moved
    cases hprm : m.mv.promo with
    | none => exact ⟨pw, hsrcb0, hsrcw', hpwk⟩
    | some k => exact ⟨⟨pw.color, k⟩, by rw [hsrcb0]; rfl, hsrcw', hpk k hprm⟩
  have hqmwk : qm ≠ ⟨.white, .king⟩ := by
    intro e
    rw [e] at hqmk
    exact hqmk rfl
  have hqmbk : qm ≠ ⟨.black, .king⟩ := by
    intro e
    rw [e] at hqmc
    exact absurd hqmc (by decide)
  cases hEP : m.ep with
  | none =>
    have he : isEp p m.mv = false := by rw [hEP] at hkE; exact hkE
    have hpb := play_board_simple p m.mv hkC he
    have hbd : (play p m.mv).board m.mv.dst = some qm := by rw [hpb, ite_eq_left rfl]; exact hqmE
    have hbsr : (play p m.mv).board m.mv.src = none := by
      rw [hpb, ite_eq_right hsd, ite_eq_left rfl]
    have hoth : ∀ x : Sq, x ≠ m.mv.dst → x ≠ m.mv.src → (play p m.mv).board x = p.board x :=
      fun x h1 h2 => by rw [hpb, ite_eq_right h1, ite_eq_right h2]
    have hskip0 : ∀ s : Sq, s ≠ m.mv.dst → s ∉ [m.mv.src] → (play p m.mv).board s = p.board s :=
      fun s h1 h2 => hoth s h1 (fun e => h2 (List.mem_singleton.mpr e))
    have hbR : ∀ s : Sq, s ∈ [m.mv.src] → (play p m.mv).board s = none := by
      intro s hs
      rw [List.mem_singleton] at hs
      subst hs
      exact hbsr
    have hbk2 : ∀ t : Sq, (play p m.mv).board t = some ⟨.black, .king⟩ ↔ t = toSq c.kb :=
      king_loc_of_play hbd hqmbk hbR hskip0 hbuniq hbb
        (fun hs => hsrc_ne_kb (((List.mem_singleton.mp hs).trans hsrce).symm))
        (fun e2 => hdst_ne_kb ((e2.trans hdstE).symm))
    have hwk2 : ∀ t : Sq, (play p m.mv).board t = some ⟨.white, .king⟩ ↔ t = toSq c.kw :=
      king_loc_of_play hbd hqmwk hbR hskip0 hwuniq hwb
        (fun hs => hsrc_ne_kw (((List.mem_singleton.mp hs).trans hsrce).symm))
        (fun e2 => hdst_ne_kw ((e2.trans hdstE).symm))
    rw [Option.toList_none]
    refine ⟨⟨?_, ?_, ?_⟩, hbk2, hwk2, ⟨qm, by rw [← hdstE]; exact hbd, hqmc⟩, ?_, ?_, ?_, ?_⟩
    · intro q hq64 hqe hqo hqx
      rw [List.mem_singleton] at hqe
      have hqd : toSq q ≠ m.mv.dst := fun e => hqo (List.mem_singleton.mpr (toSq_inj_of_lt hq64 hdst64 (e.trans hdstE)))
      have hqs : toSq q ≠ m.mv.src := fun e => hqe (toSq_inj_of_lt hq64 hsrc64 (e.trans hsrce))
      exact hoth (toSq q) hqd hqs
    · intro q hqe hqo
      rw [List.mem_singleton] at hqe
      subst hqe
      rw [← hsrce]
      exact hbsr
    · intro q hqo
      rw [List.mem_singleton] at hqo
      subst hqo
      rw [← hdstE, hbd]
      exact Option.some_ne_none qm
    · intro q hqe
      rw [List.mem_singleton] at hqe
      subst hqe
      intro hmem
      rw [List.mem_singleton] at hmem
      exact hsd' hmem
    · intro hmem
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with e1 | e1
      · exact hsrc_ne_kb (congrArg toSq e1).symm
      · exact hdst_ne_kb (congrArg toSq e1).symm
    · intro hmem
      rw [List.mem_singleton] at hmem
      exact hdst_ne_kw (congrArg toSq hmem).symm
    · intro q hqe
      rw [List.mem_singleton] at hqe
      subst hqe
      exact hsrc64
  | some e =>
    obtain ⟨hep0, hev⟩ : isEp p m.mv = true ∧ e = (epVictim m.mv).val := by
      rw [hEP] at hkE
      exact hkE
    obtain ⟨-, hpv0, -, -⟩ := pseudo_ep hA hmv hep0
    have hpv : p.board (epVictim m.mv) = some ⟨.black, .pawn⟩ := by
      have h := hpv0
      rwa [hturn] at h
    have hevSq : toSq e = epVictim m.mv := by rw [hev]; exact toSq_val _
    have hevlt : e < 64 := by rw [hev]; exact Fin.isLt _
    have hdste : p.board m.mv.dst = none := by
      have h := hep0
      unfold isEp at h
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      exact board_none_of_empty h.2
    have hv_ne_dst : epVictim m.mv ≠ m.mv.dst := by
      intro he2
      rw [← he2] at hdste
      rw [hpv] at hdste
      exact absurd hdste (by decide)
    have hv_ne_src : epVictim m.mv ≠ m.mv.src := by
      intro he2
      have h2 : p.board (epVictim m.mv) = some pw := by rw [he2]; exact hsrcb0
      rw [hpv] at h2
      obtain rfl := Option.some.inj h2
      exact absurd hsrcw' (by decide)
    have hv_ne_kw : epVictim m.mv ≠ toSq c.kw := by
      intro he2
      have h2 : p.board (epVictim m.mv) = some ⟨.white, .king⟩ := by rw [he2]; exact hwb
      rw [hpv] at h2
      exact absurd (Option.some.inj h2) (by decide)
    have hv_ne_kb : epVictim m.mv ≠ toSq c.kb := by
      intro he2
      have h2 : p.board (epVictim m.mv) = some ⟨.black, .king⟩ := by rw [he2]; exact hbb
      rw [hpv] at h2
      exact absurd (congrArg Piece.kind (Option.some.inj h2)) (by decide)
    have hpb := play_board_ep p m.mv hep0
    have hbd : (play p m.mv).board m.mv.dst = some qm := by rw [hpb, ite_eq_left rfl]; exact hqmE
    have hbsr : (play p m.mv).board m.mv.src = none := by
      rw [hpb, ite_eq_right hsd, ite_eq_left (Or.inl rfl)]
    have hbsv : (play p m.mv).board (epVictim m.mv) = none := by
      rw [hpb, ite_eq_right hv_ne_dst, ite_eq_left (Or.inr rfl)]
    have hoth : ∀ x : Sq, x ≠ m.mv.dst → x ≠ m.mv.src → x ≠ epVictim m.mv →
        (play p m.mv).board x = p.board x :=
      fun x h1 h2 h3 => by rw [hpb, ite_eq_right h1, ite_eq_right (fun h => h.elim h2 h3)]
    have hbR : ∀ s : Sq, s ∈ [m.mv.src, epVictim m.mv] → (play p m.mv).board s = none := by
      intro s hs
      rw [List.mem_cons, List.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact hbsr
      · exact hbsv
    have hskips : ∀ s : Sq, s ≠ m.mv.dst → s ∉ [m.mv.src, epVictim m.mv] →
        (play p m.mv).board s = p.board s := by
      intro s h1 h2
      exact hoth s h1 (fun e2 => h2 (List.mem_cons.mpr (Or.inl e2)))
        (fun e3 => h2 (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr e3))))
    have hbk2 : ∀ t : Sq, (play p m.mv).board t = some ⟨.black, .king⟩ ↔ t = toSq c.kb :=
      king_loc_of_play hbd hqmbk hbR hskips hbuniq hbb
        (fun hs => by
          rw [List.mem_cons, List.mem_singleton] at hs
          rcases hs with e1 | e1
          · exact hsrc_ne_kb ((e1.trans hsrce).symm)
          · exact hv_ne_kb e1.symm) (fun e2 => hdst_ne_kb ((e2.trans hdstE).symm))
    have hwk2 : ∀ t : Sq, (play p m.mv).board t = some ⟨.white, .king⟩ ↔ t = toSq c.kw :=
      king_loc_of_play hbd hqmwk hbR hskips hwuniq hwb
        (fun hs => by
          rw [List.mem_cons, List.mem_singleton] at hs
          rcases hs with e1 | e1
          · exact hsrc_ne_kw ((e1.trans hsrce).symm)
          · exact hv_ne_kw e1.symm) (fun e2 => hdst_ne_kw ((e2.trans hdstE).symm))
    rw [Option.toList_some]
    refine ⟨⟨?_, ?_, ?_⟩, hbk2, hwk2, ⟨qm, by rw [← hdstE]; exact hbd, hqmc⟩, ?_, ?_, ?_, ?_⟩
    · intro q hq64 hqe hqo hqx
      have hqs : q ≠ m.src := fun e1 => hqe (List.mem_cons.mpr (Or.inl e1))
      have hqev : q ≠ e := fun e1 => hqe (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr e1)))
      have hqdv : q ≠ m.dst := fun e1 => hqo (List.mem_singleton.mpr e1)
      exact hoth (toSq q) (fun e2 => hqdv (toSq_inj_of_lt hq64 hdst64 (e2.trans hdstE)))
        (fun e2 => hqs (toSq_inj_of_lt hq64 hsrc64 (e2.trans hsrce)))
        (fun e2 => hqev (toSq_inj_of_lt hq64 hevlt (e2.trans hevSq.symm)))
    · intro q hqe hqo
      rw [List.mem_cons, List.mem_singleton] at hqe
      rcases hqe with rfl | rfl
      · rw [← hsrce]; exact hbsr
      · rw [hevSq]; exact hbsv
    · intro q hqo
      rw [List.mem_singleton] at hqo
      subst hqo
      rw [← hdstE, hbd]
      exact Option.some_ne_none qm
    · intro q hqe
      rw [List.mem_cons, List.mem_singleton] at hqe
      intro hmem
      rw [List.mem_singleton] at hmem
      rcases hqe with rfl | rfl
      · exact hsd' hmem
      · exact hv_ne_dst ((hevSq.symm.trans (congrArg toSq hmem)).trans hdstE.symm)
    · intro hmem
      rcases List.mem_append.mp hmem with h1 | h1
      · rcases List.mem_cons.mp h1 with e1 | h1
        · exact hsrc_ne_kb (congrArg toSq e1).symm
        · exact hv_ne_kb ((congrArg toSq (List.mem_singleton.mp h1)).trans hevSq).symm
      · exact hdst_ne_kb (congrArg toSq (List.mem_singleton.mp h1)).symm
    · intro hmem
      rw [List.mem_singleton] at hmem
      exact hdst_ne_kw (congrArg toSq hmem).symm
    · intro q hqe
      rw [List.mem_cons, List.mem_singleton] at hqe
      rcases hqe with rfl | rfl
      · exact hsrc64
      · exact hevlt

theorem mkMove_legal (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (m : Cand) (hmk : m.IsMk c)
    (hr : m.src < 64 ∧ m.dst < 64 ∧ m.src ≠ c.kw ∧ m.T ≤ 4)
    (hps : m.pseudo.eval A = true → m.mv ∈ pseudo p ∧ m.KindOk p) :
    m.legal.eval A = (m.pseudo.eval A && decide (m.mv ∈ legalMoves p)) := by
  obtain ⟨hsrc64, hdst64, hkwsrc, -⟩ := hr
  have hok := fits_cfgOk hf
  obtain ⟨hkw64, hkb64, -⟩ := hok
  have hturn : p.turn = .white := hf.2.1
  have hmk' : m = c.mkMove m.src m.dst m.promo m.T m.pseudo m.ep m.w := hmk
  have hleg : m.legal = Ex.and [m.pseudo, .not (c.attB c.kw (m.src :: m.ep.toList) [m.dst] [m.dst])] :=
    (congrArg Cand.legal hmk').trans rfl
  rw [hleg]
  have hred : (Ex.and [m.pseudo, .not (c.attB c.kw (m.src :: m.ep.toList) [m.dst] [m.dst])]).eval A =
      (m.pseudo.eval A && !(c.attB c.kw (m.src :: m.ep.toList) [m.dst] [m.dst]).eval A) := by
    show (m.pseudo.eval A &&
      (!(c.attB c.kw (m.src :: m.ep.toList) [m.dst] [m.dst]).eval A && true)) = _
    rw [Bool.and_true]
  rw [hred]
  by_cases hpsv : m.pseudo.eval A = true
  · obtain ⟨hmv, hkind⟩ := hps hpsv
    have hpk : ∀ k : Kind, m.mv.promo = some k → k ≠ .king :=
      fun k hk => (pseudo_promo hmv k hk).2.2.2
    obtain ⟨hag, hbk2, hwk2, hmqm, hdisj, hko, hkwocc, hemp⟩ :=
      mk_play_facts hf m hmv hkind hsrc64 hdst64 hkwsrc hpk
    have hocc : ∀ q ∈ [m.dst], q < 64 := by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact hdst64
    have hexcl : ∀ q ∈ [m.dst], q ∈ [m.dst] ∨ q = c.kw := fun q hq => Or.inl hq
    obtain ⟨hcb1, hcb2⟩ := fits_cheb_gt_one hf
    have hkxB : cheb c.kb c.kw = 1 → c.kb ∉ [m.dst] ++ [m.dst] :=
      fun h1 => absurd (h1 ▸ hcb2) (Nat.lt_irrefl 1)
    have hattB : (c.attB c.kw (m.src :: m.ep.toList) [m.dst] [m.dst]).eval A =
        decide (∃ t : Sq, t.val ∉ [m.dst] ++ [m.dst] ∧ ∃ pc, (play p m.mv).board t = some pc ∧
          pc.color = colOf false ∧ toSq c.kw ∈ attacks (play p m.mv).board t pc) :=
      eval_att hf hg hl c.kw hkw64 false c.kb hkb64 (m.src :: m.ep.toList) [m.dst] [m.dst]
        (play p m.mv).board hag hexcl hdisj hemp hocc hbk2 hkxB hko hkwocc
    have hatt : attacked (play p m.mv).board (toSq c.kw) .black =
        decide (∃ t : Sq, t.val ∉ [m.dst] ++ [m.dst] ∧ ∃ pc, (play p m.mv).board t = some pc ∧
          pc.color = .black ∧ toSq c.kw ∈ attacks (play p m.mv).board t pc) := by
      have hiff := attacked_iff (play p m.mv).board (toSq c.kw) .black
      obtain ⟨qm0, hqm0, hqmc0⟩ := hmqm
      have hex := attExcl_of_dstColor (b' := (play p m.mv).board) (s := toSq c.kw) (d := m.dst)
        (col := .black) (fun pc hpc he => by
          rw [hqm0] at hpc
          obtain rfl := Option.some.inj hpc
          rw [hqmc0] at he
          exact absurd he (by decide))
      rw [Bool.eq_iff_iff]
      exact hiff.trans (hex.symm.trans ⟨decide_eq_true, of_decide_eq_true⟩)
    have hlink : (c.attB c.kw (m.src :: m.ep.toList) [m.dst] [m.dst]).eval A =
        attacked (play p m.mv).board (toSq c.kw) .black := hattB.trans hatt.symm
    have hbkw : (play p m.mv).board (toSq c.kw) = some ⟨.white, .king⟩ := (hwk2 (toSq c.kw)).mpr rfl
    have hinc : inCheck (play p m.mv) p.turn = attacked (play p m.mv).board (toSq c.kw) .black := by
      rw [hturn]
      unfold inCheck
      exact inCheck_eq_of_uniq hbkw (fun t ht => (hwk2 t).mp ht)
    have hmemiff : m.mv ∈ legalMoves p ↔ inCheck (play p m.mv) p.turn = false := by
      constructor
      · intro h
        exact (mem_legalMoves h).2
      · intro h
        unfold legalMoves
        rw [List.mem_filter]
        exact ⟨hmv, by rw [Bool.not_eq_true']; exact h⟩
    rw [hpsv, Bool.true_and, Bool.true_and]
    rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_true_eq]
    rw [(hlink.trans hinc.symm)]
    exact hmemiff.symm
  · have hpsv' : m.pseudo.eval A = false := Bool.eq_false_of_ne_true hpsv
    rw [hpsv', Bool.false_and, Bool.false_and]

theorem mkMove_chk (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (m : Cand) (hmk : m.IsMk c)
    (hr : m.src < 64 ∧ m.dst < 64 ∧ m.src ≠ c.kw ∧ m.T ≤ 4)
    (hmv : m.mv ∈ pseudo p) (hkind : m.KindOk p)
    (hpiece : p.board (toSq m.src) = some ⟨.white, kindOf m.T⟩)
    (hpr : ∀ k, m.promo = some k → m.T = 0 ∧ 1 ≤ k ∧ k ≤ 4) :
    m.chk.eval A = givesCheck p m.mv := by
  obtain ⟨hsrc64, hdst64, hkwsrc, hT4⟩ := hr
  have hok := fits_cfgOk hf
  obtain ⟨hkw64, hkb64, -⟩ := hok
  have hturn : p.turn = .white := hf.2.1
  obtain ⟨hkC, hkE⟩ := hkind
  have hsrce : m.mv.src = toSq m.src := rfl
  have hdstE : m.mv.dst = toSq m.dst := rfl
  have hprE : m.mv.promo = m.promo.map kindOf := rfl
  have hpk : ∀ k : Kind, m.mv.promo = some k → k ≠ .king := by
    intro kK hk
    rw [hprE] at hk
    cases hpo : m.promo with
    | none => rw [hpo, Option.map_none] at hk; simp at hk
    | some kN =>
      rw [hpo, Option.map_some] at hk
      obtain ⟨-, h1, h4⟩ := hpr kN hpo
      have hkK : kK = kindOf kN := (Option.some.inj hk).symm
      subst hkK
      rcases (show kN = 1 ∨ kN = 2 ∨ kN = 3 ∨ kN = 4 from by omega) with rfl | rfl | rfl | rfl <;>
        decide
  obtain ⟨hag, hbk2, hwk2, hmqm, hdisj, hko, hkwocc, hemp⟩ :=
    mk_play_facts hf m hmv ⟨hkC, hkE⟩ hsrc64 hdst64 hkwsrc hpk
  have hmvP : (play p m.mv).board m.mv.dst = moved p m.mv := by
    cases hEP : m.ep with
    | none =>
      have he : isEp p m.mv = false := by rw [hEP] at hkE; exact hkE
      rw [play_board_simple p m.mv hkC he, ite_eq_left rfl]
    | some e =>
      obtain ⟨hep0, -⟩ : isEp p m.mv = true ∧ e = (epVictim m.mv).val := by rw [hEP] at hkE; exact hkE
      rw [play_board_ep p m.mv hep0, ite_eq_left rfl]
  have hmovedEq : moved p m.mv = some ⟨.white, kindOf (m.promo.getD m.T)⟩ := by
    unfold moved
    rw [hprE]
    cases hpo : m.promo with
    | none =>
      show p.board m.mv.src = some ⟨.white, kindOf m.T⟩
      rw [hsrce]
      exact hpiece
    | some kN =>
      show (p.board m.mv.src).map (fun q => (⟨q.color, kindOf kN⟩ : Piece)) = some ⟨.white, kindOf kN⟩
      rw [hsrce, hpiece]
      rfl
  have hmvd : (play p m.mv).board (toSq m.dst) = some ⟨.white, kindOf (m.promo.getD m.T)⟩ := by
    rw [← hdstE, hmvP, hmovedEq]
  have hT' : m.promo.getD m.T ≤ 4 := by
    cases hpo : m.promo with
    | none => exact hT4
    | some kN => exact (hpr kN hpo).2.2
  obtain ⟨hcb1, -⟩ := fits_cheb_gt_one hf
  have hkxW : cheb c.kw c.kb = 1 → c.kw ∉ [m.dst] ++ [m.dst] :=
    fun h1 => absurd (h1 ▸ hcb1) (Nat.lt_irrefl 1)
  have hocc : ∀ q ∈ [m.dst], q < 64 := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hdst64
  have hexcl : ∀ q ∈ [m.dst], q ∈ [m.dst] ∨ q = c.kb := fun q hq => Or.inl hq
  have hdirE : ∀ q ∈ between m.dst c.kb, q ∉ m.src :: m.ep.toList → q ∉ [] →
      (play p m.mv).board (toSq q) = p.board (toSq q) := by
    intro q hq hqe _
    have hqne : q ≠ m.dst := (mem_between_ne hdst64 hkb64 hq).1
    exact hag.1 q (between_lt64 hq) hqe (mem_singleton_ne hqne) (mem_singleton_ne hqne)
  have hdirE2 : ∀ q ∈ between m.dst c.kb, q ∈ m.src :: m.ep.toList → q ∉ [] →
      (play p m.mv).board (toSq q) = none := by
    intro q hq hqe _
    have hqne : q ≠ m.dst := (mem_between_ne hdst64 hkb64 hq).1
    exact hag.2.1 q hqe (mem_singleton_ne hqne)
  have hdir : (c.direct m.dst (m.promo.getD m.T) (m.src :: m.ep.toList) []).eval A =
      (attacks (play p m.mv).board (toSq m.dst) ⟨.white, kindOf (m.promo.getD m.T)⟩).contains
        (toSq c.kb) :=
    eval_direct hf hg hl m.dst (m.promo.getD m.T) hdst64 hT' (m.src :: m.ep.toList) []
      (play p m.mv).board (fun q _ h2 => absurd h2 (by simp)) hdirE hdirE2 (fun q _ h2 => absurd h2 (by simp))
  have hattW : (c.attW c.kb (m.src :: m.ep.toList) [m.dst] [m.dst]).eval A =
      decide (∃ t : Sq, t.val ∉ [m.dst] ++ [m.dst] ∧ ∃ pc, (play p m.mv).board t = some pc ∧
        pc.color = colOf true ∧ toSq c.kb ∈ attacks (play p m.mv).board t pc) :=
    eval_att hf hg hl c.kb hkb64 true c.kw hkw64 (m.src :: m.ep.toList) [m.dst] [m.dst]
      (play p m.mv).board hag hexcl hdisj hemp hocc hwk2 hkxW hko hkwocc
  have hchkE : m.chk = Ex.or [c.direct m.dst (m.promo.getD m.T) (m.src :: m.ep.toList) [],
      c.attW c.kb (m.src :: m.ep.toList) [m.dst] [m.dst]] :=
    (congrArg Cand.chk (show m = c.mkMove m.src m.dst m.promo m.T m.pseudo m.ep m.w from hmk)).trans rfl
  rw [hchkE]
  have hred : (Ex.or [c.direct m.dst (m.promo.getD m.T) (m.src :: m.ep.toList) [],
      c.attW c.kb (m.src :: m.ep.toList) [m.dst] [m.dst]]).eval A =
      ((c.direct m.dst (m.promo.getD m.T) (m.src :: m.ep.toList) []).eval A ||
        (c.attW c.kb (m.src :: m.ep.toList) [m.dst] [m.dst]).eval A) := by
    show ((c.direct m.dst (m.promo.getD m.T) (m.src :: m.ep.toList) []).eval A ||
      ((c.attW c.kb (m.src :: m.ep.toList) [m.dst] [m.dst]).eval A || false)) = _
    rw [Bool.or_false]
  rw [hred]
  have hPD : (c.direct m.dst (m.promo.getD m.T) (m.src :: m.ep.toList) []).eval A =
      decide (toSq c.kb ∈ attacks (play p m.mv).board (toSq m.dst) ⟨.white, kindOf (m.promo.getD m.T)⟩) := by
    rw [hdir, Bool.eq_iff_iff, decide_eq_true_eq]
    exact List.contains_iff_mem
  have hgc : givesCheck p m.mv = attacked (play p m.mv).board (toSq c.kb) .white := by
    show inCheck (play p m.mv) p.turn.opp = _
    rw [hturn]
    unfold inCheck
    exact inCheck_eq_of_uniq (c := Color.opp .white) ((hbk2 (toSq c.kb)).mpr rfl)
      (fun t ht => (hbk2 t).mp ht)
  have hWA : attacked (play p m.mv).board (toSq c.kb) .white =
      decide (∃ t pc, (play p m.mv).board t = some pc ∧ pc.color = .white ∧
        toSq c.kb ∈ attacks (play p m.mv).board t pc) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    exact attacked_iff (play p m.mv).board (toSq c.kb) .white
  have hsplit := attSplit_dst (b' := (play p m.mv).board) (s := toSq c.kb) (d := m.dst) (col := .white)
    (pc0 := ⟨.white, kindOf (m.promo.getD m.T)⟩) hmvd rfl
  rw [hgc, hWA, hPD, hattW, Bool.eq_iff_iff, decide_eq_true_eq, Bool.or_eq_true, decide_eq_true_eq,
    decide_eq_true_eq]
  exact hsplit.symm

theorem cheb_self (a : Nat) : cheb a a = 0 := by
  show max ((fr a).1 - (fr a).1).natAbs ((fr a).2 - (fr a).2).natAbs = 0
  have h1 : ((fr a).1 - (fr a).1 : Int) = 0 := by omega
  have h2 : ((fr a).2 - (fr a).2 : Int) = 0 := by omega
  rw [h1, h2]
  decide

theorem eval_and4 (A : Assignment) (a b d e : Ex) :
    (Ex.and [a, b, d, e]).eval A = (a.eval A && (b.eval A && (d.eval A && e.eval A))) := by
  simp [Ex.eval, Ex.evalAll]

theorem eval_and5 (A : Assignment) (a b d e f : Ex) :
    (Ex.and [a, b, d, e, f]).eval A = (a.eval A && (b.eval A && (d.eval A && (e.eval A && f.eval A)))) := by
  simp [Ex.eval, Ex.evalAll]

theorem eval_and6 (A : Assignment) (a b d e f g : Ex) :
    (Ex.and [a, b, d, e, f, g]).eval A =
      (a.eval A && (b.eval A && (d.eval A && (e.eval A && (f.eval A && g.eval A))))) := by
  simp [Ex.eval, Ex.evalAll]

theorem eval_and7 (A : Assignment) (a b d e f g i : Ex) :
    (Ex.and [a, b, d, e, f, g, i]).eval A =
      (a.eval A && (b.eval A && (d.eval A && (e.eval A && (f.eval A && (g.eval A && i.eval A)))))) := by
  simp [Ex.eval, Ex.evalAll]

theorem eval_or2 (A : Assignment) (a b : Ex) :
    (Ex.or [a, b]).eval A = (a.eval A || b.eval A) := by simp [Ex.eval, Ex.evalAny]

theorem mem_of_mem_takeWhile {l : List Nat} {p : Nat → Bool} {x : Nat} (h : x ∈ l.takeWhile p) :
    x ∈ l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    by_cases hy : p y = true
    · rw [List.takeWhile_cons_of_pos (p := p) hy, List.mem_cons] at h
      rcases h with h | h
      · subst h
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem y (ih h)
    · rw [List.takeWhile_cons_of_neg (p := p) hy] at h
      simp at h

theorem takeWhile_subset_of_mem {l : List Nat} {e F : Nat} (he : e ∈ l.takeWhile (· != F)) :
    ∀ u ∈ l.takeWhile (· != e), u ∈ l.takeWhile (· != F) := by
  induction l with
  | nil => intro u hu; exact hu
  | cons y ys ih =>
    intro u hu
    by_cases hyF : (y != F) = true
    · rw [List.takeWhile_cons_of_pos (p := (· != F)) hyF] at he
      rw [List.takeWhile_cons_of_pos (p := (· != F)) hyF]
      rw [List.mem_cons] at he
      rcases he with he | he
      · subst he
        rw [List.takeWhile_cons_of_neg (p := (· != e)) (by simp)] at hu
        simp at hu
      · by_cases hye : (y != e) = true
        · rw [List.takeWhile_cons_of_pos (p := (· != e)) hye, List.mem_cons] at hu
          rw [List.mem_cons]
          rcases hu with hu | hu
          · exact Or.inl hu
          · exact Or.inr (ih he u hu)
        · rw [List.takeWhile_cons_of_neg (p := (· != e)) hye] at hu
          simp at hu
    · rw [List.takeWhile_cons_of_neg (p := (· != F)) hyF] at he
      simp at he

theorem kingCands_unpack {m : Cand} (hm : m ∈ c.kingCands) :
    ∃ t, t < 64 ∧ cheb c.kw t = 1 ∧ 1 < cheb c.kb t ∧ m =
      { src := c.kw, dst := t, promo := none, T := 5, ep := none, pseudo := Ex.not (c.wocc t),
        w := 1, skip := false,
        legal := Ex.and [Ex.not (c.wocc t), Ex.not (c.attB t [c.kw] [] [t])],
        chk := c.attW c.kb [c.kw] [t] [t] t : Cand } := by
  obtain ⟨t, ht, hfe⟩ := List.mem_filterMap.mp
    (show m ∈ (List.range 64).filterMap _ from hm)
  rw [List.mem_range] at ht
  dsimp only at hfe
  split at hfe
  · next hcond =>
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff] at hcond
    exact ⟨t, ht, hcond.1, hcond.2, (Option.some.inj hfe).symm⟩
  · simp at hfe

theorem castleCands_unpack {m : Cand} (hm : m ∈ c.castleCands r) :
    (∃ v, r.cr.lookup true = some v ∧ m = c.castleK v) ∨
      (∃ v, r.cr.lookup false = some v ∧ m = c.castleQ v) := by
  rcases List.mem_append.mp (show m ∈ (r.cr.lookup true).toList.map c.castleK ++
    (r.cr.lookup false).toList.map c.castleQ from hm) with hm | hm
  · obtain ⟨v, hv, hmv⟩ := List.mem_map.mp hm
    exact Or.inl ⟨v, Option.mem_toList.mp hv, hmv.symm⟩
  · obtain ⟨v, hv, hmv⟩ := List.mem_map.mp hm
    exact Or.inr ⟨v, Option.mem_toList.mp hv, hmv.symm⟩

theorem king_play_facts (hf : Fits c p) (t : Nat) (ht : t < 64)
    (hc1 : cheb c.kw t = 1) (hc2 : 1 < cheb c.kb t) :
    (∀ s : Sq, (play p ⟨toSq c.kw, toSq t, none⟩).board s = if s = toSq t then some ⟨.white, .king⟩
        else if s = toSq c.kw then none else p.board s)
      ∧ (∀ s : Sq, (play p ⟨toSq c.kw, toSq t, none⟩).board s = some ⟨.white, .king⟩ ↔ s = toSq t)
      ∧ (∀ s : Sq, (play p ⟨toSq c.kw, toSq t, none⟩).board s = some ⟨.black, .king⟩ ↔ s = toSq c.kb)
      ∧ (play p ⟨toSq c.kw, toSq t, none⟩).board (toSq t) = some ⟨.white, .king⟩
      ∧ (play p ⟨toSq c.kw, toSq t, none⟩).board (toSq c.kb) = some ⟨.black, .king⟩ := by
  have hok := fits_cfgOk hf
  obtain ⟨hkw64, hkb64, hcheb12⟩ := hok
  obtain ⟨hpwb, hpbb, hsym⟩ := fits_kings hf
  have hA := hf.1
  have hkwv : (kingSq p .white).val = c.kw := congrArg Cfg.kw hf.2.2
  have hkbv : (kingSq p .black).val = c.kb := congrArg Cfg.kb hf.2.2
  have hkw2 : toSq c.kw = kingSq p .white :=
    Fin.ext (by rw [toSq_val_of_lt c.kw hkw64]; exact hkwv.symm)
  have hkb2 : toSq c.kb = kingSq p .black :=
    Fin.ext (by rw [toSq_val_of_lt c.kb hkb64]; exact hkbv.symm)
  have hpwu : ∀ s : Sq, p.board s = some ⟨.white, .king⟩ → s = toSq c.kw :=
    fun s hs => ((kingSq_spec p .white (hA.kings .white)).2 s hs).trans hkw2.symm
  have hpbu : ∀ s : Sq, p.board s = some ⟨.black, .king⟩ → s = toSq c.kb :=
    fun s hs => ((kingSq_spec p .black (hA.kings .black)).2 s hs).trans hkb2.symm
  have ht_ne : t ≠ c.kw := by
    intro e
    rw [e, cheb_self] at hc1
    exact absurd hc1 (by decide)
  have hkbnt : c.kb ≠ t := by
    intro e
    rw [e, cheb_self] at hc2
    exact absurd hc2 (by omega)
  have hkbnkw : c.kb ≠ c.kw := by
    intro e
    rw [e, cheb_self] at hcheb12
    exact absurd hcheb12 (by omega)
  have hchebd : dist (toSq c.kw) (toSq t) = 1 := by
    rw [← cheb_toSq c.kw t hkw64 ht]
    exact hc1
  have hcastf : isCastle p ⟨toSq c.kw, toSq t, none⟩ = false := by
    have hf1 : ((toSq c.kw).file + 2 == (toSq t).file) = false := by
      rw [beq_eq_false_iff_ne]
      unfold dist at hchebd
      omega
    have hf2 : ((toSq t).file + 2 == (toSq c.kw).file) = false := by
      rw [beq_eq_false_iff_ne]
      unfold dist at hchebd
      omega
    show ((p.board (toSq c.kw)).any (·.kind == .king) &&
      ((toSq c.kw).file + 2 == (toSq t).file || (toSq t).file + 2 == (toSq c.kw).file)) = false
    rw [hf1, hf2]
    exact Bool.and_false _
  have hanyK : (p.board (toSq c.kw)).any (·.kind == .king) = true := by
    rw [hpwb]
    rfl
  have hEpf : isEp p ⟨toSq c.kw, toSq t, none⟩ = false := by
    show ((p.board (toSq c.kw)).any (·.kind == .pawn) && (toSq c.kw).file != (toSq t).file &&
      empty p.board (toSq t)) = false
    rw [any_kind_ne p.board (toSq c.kw) .king .pawn hanyK (by decide)]
    rfl
  have hpb : ∀ s : Sq, (play p ⟨toSq c.kw, toSq t, none⟩).board s =
      if s = toSq t then some ⟨.white, .king⟩ else if s = toSq c.kw then none else p.board s := by
    intro s
    rw [play_board_simple p ⟨toSq c.kw, toSq t, none⟩ hcastf hEpf s]
    show (if s = toSq t then moved p ⟨toSq c.kw, toSq t, none⟩
        else if s = toSq c.kw then none else p.board s) = _
    rw [show moved p ⟨toSq c.kw, toSq t, none⟩ = some ⟨.white, .king⟩ from hpwb]
  have hsw : (play p ⟨toSq c.kw, toSq t, none⟩).board (toSq t) = some ⟨.white, .king⟩ := by
    rw [hpb (toSq t), if_pos rfl]
  have hsb : (play p ⟨toSq c.kw, toSq t, none⟩).board (toSq c.kb) = some ⟨.black, .king⟩ := by
    rw [hpb (toSq c.kb), if_neg (fun e => hkbnt (toSq_inj_of_lt hkb64 ht e)),
      if_neg (fun e => hkbnkw (toSq_inj_of_lt hkb64 hkw64 e))]
    exact hpbb
  refine ⟨hpb, ?_, ?_, hsw, hsb⟩
  · intro s
    rw [hpb s]
    by_cases hst : s = toSq t
    · rw [if_pos hst]
      exact ⟨fun _ => hst, fun _ => rfl⟩
    · rw [if_neg hst]
      by_cases hsk : s = toSq c.kw
      · rw [if_pos hsk]
        constructor
        · intro hh
          simp at hh
        · intro hh
          exact absurd hh hst
      · rw [if_neg hsk]
        exact ⟨fun hh => absurd (hpwu s hh) hsk, fun hh => absurd hh hst⟩
  · intro s
    rw [hpb s]
    by_cases hst : s = toSq t
    · rw [if_pos hst]
      constructor
      · intro hh
        have h2 := Option.some.inj hh
        simp only [Piece.mk.injEq] at h2
        exact absurd h2.1 (by decide)
      · intro hh
        exact absurd (toSq_inj_of_lt ht hkb64 (hst ▸ hh)).symm hkbnt
    · rw [if_neg hst]
      by_cases hsk : s = toSq c.kw
      · rw [if_pos hsk]
        constructor
        · intro hh
          simp at hh
        · intro hh
          exact absurd (toSq_inj_of_lt hkw64 hkb64 (hsk ▸ hh)) (fun e => hkbnkw e.symm)
      · rw [if_neg hsk]
        exact ⟨hpbu s, fun hh => hh ▸ hpbb⟩

theorem direction_self (a : Nat) : direction a a = none := by
  unfold direction
  have h1 : ((fr a).1 - (fr a).1 : Int) = 0 := by omega
  have h2 : ((fr a).2 - (fr a).2 : Int) = 0 := by omega
  rw [h1, h2]
  decide

theorem mem_of_mem_takeWhile_p {l : List Nat} {p : Nat → Bool} {x : Nat} (h : x ∈ l.takeWhile p) :
    p x = true :=
  List.all_eq_true.mp List.all_takeWhile x h

theorem between_dir_of_mem {t F e : Nat} (ht : t < 64) (hF : F < 64) (he : e ∈ between t F) :
    ∃ d, direction t F = some d ∧ direction t e = some d ∧
      (∀ u ∈ between t e, u ∈ between t F) ∧ e ≠ F ∧ e < 64 := by
  have hne := mem_between_ne ht hF he
  unfold between at he
  split at he
  · simp at he
  · next d hdir =>
    dsimp only at he
    split at he
    · next hcont =>
      have heRl : e ∈ rayL t d := mem_of_mem_takeWhile he
      have he64 : e < 64 := rayL_lt64 heRl
      have hdmem : d ∈ orth ++ diag := direction_mem hdir
      have hdirTE : direction t e = some d := (mem_rayL_iff t e ht he64 d hdmem).mp heRl
      have hce : (rayL t d).contains e = true := List.contains_iff_mem.mpr heRl
      have hbF : between t F = (rayL t d).takeWhile (· != F) := by
        unfold between
        rw [hdir]
        dsimp only
        rw [if_pos hcont]
      have hbE : between t e = (rayL t d).takeWhile (· != e) := by
        unfold between
        rw [hdirTE]
        dsimp only
        rw [if_pos hce]
      exact ⟨d, hdir, hdirTE, fun u hu => hbF.symm ▸ takeWhile_subset_of_mem he u (hbE ▸ hu), hne.2, he64⟩
    · next hnc =>
      simp at he

theorem chess_self_attack (b : Board) (s : Sq) (pc : Piece) : s ∉ attacks b s pc := by
  obtain ⟨cl, kd⟩ := pc
  intro h
  cases kd with
  | pawn =>
    obtain ⟨h1, -⟩ := (mem_attacks_pawn b s s cl).mp h
    cases cl with
    | white =>
      have h2 : (Color.fwd .white : Int) = 1 := rfl
      rw [h2] at h1
      omega
    | black =>
      have h2 : (Color.fwd .black : Int) = -1 := rfl
      rw [h2] at h1
      omega
  | knight =>
    rw [mem_attacks_knight] at h
    simp only [knightL, List.mem_filterMap] at h
    obtain ⟨d, hd, hos⟩ := h
    obtain ⟨hfr1, hfr2⟩ := sqo_fr hos
    simp only [kn, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd | hd <;> subst hd <;> omega
  | king =>
    rw [mem_attacks_king, cheb_self] at h
    exact absurd h (by decide)
  | bishop =>
    obtain ⟨d, hdir, -, -⟩ := (mem_attacks_slider b s s ⟨cl, .bishop⟩ (Or.inl rfl)).mp h
    rw [direction_self] at hdir
    simp at hdir
  | rook =>
    obtain ⟨d, hdir, -, -⟩ := (mem_attacks_slider b s s ⟨cl, .rook⟩ (Or.inr (Or.inl rfl))).mp h
    rw [direction_self] at hdir
    simp at hdir
  | queen =>
    obtain ⟨d, hdir, -, -⟩ := (mem_attacks_slider b s s ⟨cl, .queen⟩ (Or.inr (Or.inr rfl))).mp h
    rw [direction_self] at hdir
    simp at hdir

theorem mem_attacks_congr {b₁ b₂ : Board} {t s : Sq} {pc : Piece} (hts : t ≠ s)
    (h : ∀ u, u ≠ s → b₁ u = b₂ u) : s ∈ attacks b₁ t pc ↔ s ∈ attacks b₂ t pc := by
  obtain ⟨cl, kd⟩ := pc
  have hbtw : ∀ u ∈ between t.val s.val, (b₁ (toSq u) = none ↔ b₂ (toSq u) = none) := by
    intro u hu
    have huv : u ≠ s.val := (mem_between_ne t.isLt s.isLt hu).2
    have hus : toSq u ≠ s := fun e =>
      huv ((toSq_val_of_lt u (between_lt64 hu)).symm.trans (congrArg Fin.val e))
    exact ⟨fun hh => h (toSq u) hus ▸ hh, fun hh => (h (toSq u) hus).symm ▸ hh⟩
  cases kd with
  | pawn => exact Iff.rfl
  | knight => exact Iff.rfl
  | king => exact Iff.rfl
  | bishop =>
    constructor
    · intro hh
      obtain ⟨d, hdir, hk, hcl⟩ := (mem_attacks_slider b₁ t s ⟨cl, .bishop⟩ (Or.inl rfl)).mp hh
      exact (mem_attacks_slider b₂ t s ⟨cl, .bishop⟩ (Or.inl rfl)).mpr
        ⟨d, hdir, hk, fun u hu => (hbtw u hu).mp (hcl u hu)⟩
    · intro hh
      obtain ⟨d, hdir, hk, hcl⟩ := (mem_attacks_slider b₂ t s ⟨cl, .bishop⟩ (Or.inl rfl)).mp hh
      exact (mem_attacks_slider b₁ t s ⟨cl, .bishop⟩ (Or.inl rfl)).mpr
        ⟨d, hdir, hk, fun u hu => (hbtw u hu).mpr (hcl u hu)⟩
  | rook =>
    constructor
    · intro hh
      obtain ⟨d, hdir, hk, hcl⟩ := (mem_attacks_slider b₁ t s ⟨cl, .rook⟩ (Or.inr (Or.inl rfl))).mp hh
      exact (mem_attacks_slider b₂ t s ⟨cl, .rook⟩ (Or.inr (Or.inl rfl))).mpr
        ⟨d, hdir, hk, fun u hu => (hbtw u hu).mp (hcl u hu)⟩
    · intro hh
      obtain ⟨d, hdir, hk, hcl⟩ := (mem_attacks_slider b₂ t s ⟨cl, .rook⟩ (Or.inr (Or.inl rfl))).mp hh
      exact (mem_attacks_slider b₁ t s ⟨cl, .rook⟩ (Or.inr (Or.inl rfl))).mpr
        ⟨d, hdir, hk, fun u hu => (hbtw u hu).mpr (hcl u hu)⟩
  | queen =>
    constructor
    · intro hh
      obtain ⟨d, hdir, hk, hcl⟩ := (mem_attacks_slider b₁ t s ⟨cl, .queen⟩ (Or.inr (Or.inr rfl))).mp hh
      exact (mem_attacks_slider b₂ t s ⟨cl, .queen⟩ (Or.inr (Or.inr rfl))).mpr
        ⟨d, hdir, hk, fun u hu => (hbtw u hu).mp (hcl u hu)⟩
    · intro hh
      obtain ⟨d, hdir, hk, hcl⟩ := (mem_attacks_slider b₂ t s ⟨cl, .queen⟩ (Or.inr (Or.inr rfl))).mp hh
      exact (mem_attacks_slider b₁ t s ⟨cl, .queen⟩ (Or.inr (Or.inr rfl))).mpr
        ⟨d, hdir, hk, fun u hu => (hbtw u hu).mpr (hcl u hu)⟩

theorem attacked_congr_off {b₁ b₂ : Board} {s : Sq} {c : Color} (h : ∀ t, t ≠ s → b₁ t = b₂ t) :
    attacked b₁ s c = attacked b₂ s c := by
  have key : (∃ t pc, b₁ t = some pc ∧ pc.color = c ∧ s ∈ attacks b₁ t pc) ↔
      (∃ t pc, b₂ t = some pc ∧ pc.color = c ∧ s ∈ attacks b₂ t pc) := by
    constructor
    · rintro ⟨t, pc, hb, hc, ha⟩
      by_cases hts : t = s
      · exact absurd (hts ▸ ha) (chess_self_attack b₁ s pc)
      · exact ⟨t, pc, h t hts ▸ hb, hc, (mem_attacks_congr hts h).mp ha⟩
    · rintro ⟨t, pc, hb, hc, ha⟩
      by_cases hts : t = s
      · exact absurd (hts ▸ ha) (chess_self_attack b₂ s pc)
      · exact ⟨t, pc, (h t hts).symm ▸ hb, hc, (mem_attacks_congr hts (fun u hu => (h u hu).symm)).mp ha⟩
  rw [Bool.eq_iff_iff, attacked_iff, attacked_iff]
  exact key

theorem attacked_vac {b : Board} {e F : Sq} {c : Color}
    (hn : ∀ pc, b e = some pc → pc.color ≠ c) (hsafe : attacked b e c = false) :
    attacked (fun t => if t = e then none else b t) F c = attacked b F c := by
  have key : (∃ t pc, (fun t => if t = e then none else b t) t = some pc ∧ pc.color = c ∧
        F ∈ attacks (fun t => if t = e then none else b t) t pc) ↔
      (∃ t pc, b t = some pc ∧ pc.color = c ∧ F ∈ attacks b t pc) := by
    constructor
    · rintro ⟨t, pc, hb, hc, ha⟩
      have hb2 : (if t = e then none else b t) = some pc := hb
      have hte : t ≠ e := by
        intro e2
        subst e2
        rw [if_pos rfl] at hb2
        simp at hb2
      rw [if_neg hte] at hb2
      refine ⟨t, pc, hb2, hc, ?_⟩
      obtain ⟨cl, kd⟩ := pc
      cases kd with
      | pawn => exact ha
      | knight => exact ha
      | king => exact ha
      | bishop =>
        obtain ⟨d, hdir, hkd, hclear⟩ := (mem_attacks_slider _ t F ⟨cl, .bishop⟩ (Or.inl rfl)).mp ha
        refine (mem_attacks_slider b t F ⟨cl, .bishop⟩ (Or.inl rfl)).mpr ⟨d, hdir, hkd, fun u hu => ?_⟩
        by_cases hu2 : toSq u = e
        · exfalso
          have huEV : u = e.val := by
            have h1 := toSq_val_of_lt u (between_lt64 hu)
            have h2 := congrArg Fin.val hu2
            rw [h1] at h2
            exact h2
          obtain ⟨d', hdirTF, hdirTE, hsub, -, he64⟩ := between_dir_of_mem t.isLt F.isLt (huEV ▸ hu)
          have hdE : d' = d := Option.some.inj (hdirTF.symm.trans hdir)
          rw [hdE] at hdirTE
          have hsafe2 : attacked b e c = true := by
            rw [attacked_iff]
            refine ⟨t, ⟨cl, .bishop⟩, hb2, hc, (mem_attacks_slider b t e ⟨cl, .bishop⟩ (Or.inl rfl)).mpr
              ⟨d, hdirTE, hkd, fun u' hu' => ?_⟩⟩
            have huE2 : u' ≠ e.val := (mem_between_ne t.isLt he64 hu').2
            have htu : toSq u' ≠ e := fun ee =>
              huE2 ((toSq_val_of_lt u' (between_lt64 hu')).symm.trans (congrArg Fin.val ee))
            have h3 : (if toSq u' = e then none else b (toSq u')) = none :=
              hclear u' (hsub u' hu')
            rw [if_neg htu] at h3
            exact h3
          rw [hsafe] at hsafe2
          exact absurd hsafe2 (by decide)
        · have h3 : (if toSq u = e then none else b (toSq u)) = none := hclear u hu
          rw [if_neg hu2] at h3
          exact h3
      | rook =>
        obtain ⟨d, hdir, hkd, hclear⟩ :=
          (mem_attacks_slider _ t F ⟨cl, .rook⟩ (Or.inr (Or.inl rfl))).mp ha
        refine (mem_attacks_slider b t F ⟨cl, .rook⟩ (Or.inr (Or.inl rfl))).mpr
          ⟨d, hdir, hkd, fun u hu => ?_⟩
        by_cases hu2 : toSq u = e
        · exfalso
          have huEV : u = e.val := by
            have h1 := toSq_val_of_lt u (between_lt64 hu)
            have h2 := congrArg Fin.val hu2
            rw [h1] at h2
            exact h2
          obtain ⟨d', hdirTF, hdirTE, hsub, -, he64⟩ := between_dir_of_mem t.isLt F.isLt (huEV ▸ hu)
          have hdE : d' = d := Option.some.inj (hdirTF.symm.trans hdir)
          rw [hdE] at hdirTE
          have hsafe2 : attacked b e c = true := by
            rw [attacked_iff]
            refine ⟨t, ⟨cl, .rook⟩, hb2, hc, (mem_attacks_slider b t e ⟨cl, .rook⟩ (Or.inr (Or.inl rfl))).mpr
              ⟨d, hdirTE, hkd, fun u' hu' => ?_⟩⟩
            have huE2 : u' ≠ e.val := (mem_between_ne t.isLt he64 hu').2
            have htu : toSq u' ≠ e := fun ee =>
              huE2 ((toSq_val_of_lt u' (between_lt64 hu')).symm.trans (congrArg Fin.val ee))
            have h3 : (if toSq u' = e then none else b (toSq u')) = none :=
              hclear u' (hsub u' hu')
            rw [if_neg htu] at h3
            exact h3
          rw [hsafe] at hsafe2
          exact absurd hsafe2 (by decide)
        · have h3 : (if toSq u = e then none else b (toSq u)) = none := hclear u hu
          rw [if_neg hu2] at h3
          exact h3
      | queen =>
        obtain ⟨d, hdir, hkd, hclear⟩ :=
          (mem_attacks_slider _ t F ⟨cl, .queen⟩ (Or.inr (Or.inr rfl))).mp ha
        refine (mem_attacks_slider b t F ⟨cl, .queen⟩ (Or.inr (Or.inr rfl))).mpr
          ⟨d, hdir, hkd, fun u hu => ?_⟩
        by_cases hu2 : toSq u = e
        · exfalso
          have huEV : u = e.val := by
            have h1 := toSq_val_of_lt u (between_lt64 hu)
            have h2 := congrArg Fin.val hu2
            rw [h1] at h2
            exact h2
          obtain ⟨d', hdirTF, hdirTE, hsub, -, he64⟩ := between_dir_of_mem t.isLt F.isLt (huEV ▸ hu)
          have hdE : d' = d := Option.some.inj (hdirTF.symm.trans hdir)
          rw [hdE] at hdirTE
          have hsafe2 : attacked b e c = true := by
            rw [attacked_iff]
            refine ⟨t, ⟨cl, .queen⟩, hb2, hc,
              (mem_attacks_slider b t e ⟨cl, .queen⟩ (Or.inr (Or.inr rfl))).mpr
              ⟨d, hdirTE, hkd, fun u' hu' => ?_⟩⟩
            have huE2 : u' ≠ e.val := (mem_between_ne t.isLt he64 hu').2
            have htu : toSq u' ≠ e := fun ee =>
              huE2 ((toSq_val_of_lt u' (between_lt64 hu')).symm.trans (congrArg Fin.val ee))
            have h3 : (if toSq u' = e then none else b (toSq u')) = none :=
              hclear u' (hsub u' hu')
            rw [if_neg htu] at h3
            exact h3
          rw [hsafe] at hsafe2
          exact absurd hsafe2 (by decide)
        · have h3 : (if toSq u = e then none else b (toSq u)) = none := hclear u hu
          rw [if_neg hu2] at h3
          exact h3
    · rintro ⟨t, pc, hb, hc, ha⟩
      have hte : t ≠ e := by
        intro e2
        subst e2
        exact hn pc hb hc
      refine ⟨t, pc, ?_, hc, ?_⟩
      · show (if t = e then none else b t) = some pc
        rw [if_neg hte]
        exact hb
      · obtain ⟨cl, kd⟩ := pc
        cases kd with
        | pawn => exact ha
        | knight => exact ha
        | king => exact ha
        | bishop =>
          obtain ⟨d, hdir, hkd, hclear⟩ := (mem_attacks_slider b t F ⟨cl, .bishop⟩ (Or.inl rfl)).mp ha
          refine (mem_attacks_slider _ t F ⟨cl, .bishop⟩ (Or.inl rfl)).mpr ⟨d, hdir, hkd, fun u hu => ?_⟩
          have h2 : (if toSq u = e then none else b (toSq u)) = none := by
            by_cases hu2 : toSq u = e
            · rw [if_pos hu2]
            · rw [if_neg hu2]
              exact hclear u hu
          exact h2
        | rook =>
          obtain ⟨d, hdir, hkd, hclear⟩ := (mem_attacks_slider b t F ⟨cl, .rook⟩ (Or.inr (Or.inl rfl))).mp ha
          refine (mem_attacks_slider _ t F ⟨cl, .rook⟩ (Or.inr (Or.inl rfl))).mpr ⟨d, hdir, hkd, fun u hu => ?_⟩
          have h2 : (if toSq u = e then none else b (toSq u)) = none := by
            by_cases hu2 : toSq u = e
            · rw [if_pos hu2]
            · rw [if_neg hu2]
              exact hclear u hu
          exact h2
        | queen =>
          obtain ⟨d, hdir, hkd, hclear⟩ := (mem_attacks_slider b t F ⟨cl, .queen⟩ (Or.inr (Or.inr rfl))).mp ha
          refine (mem_attacks_slider _ t F ⟨cl, .queen⟩ (Or.inr (Or.inr rfl))).mpr ⟨d, hdir, hkd, fun u hu => ?_⟩
          have h2 : (if toSq u = e then none else b (toSq u)) = none := by
            by_cases hu2 : toSq u = e
            · rw [if_pos hu2]
            · rw [if_neg hu2]
              exact hclear u hu
          exact h2
  rw [Bool.eq_iff_iff, attacked_iff, attacked_iff]
  exact key

theorem eval_attB_vac (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (E F : Nat)
    (hF : F < 64) (hEkw : E = c.kw) :
    (c.attB F [E] [] []).eval A = attacked (fun t => if t = toSq E then none else p.board t) (toSq F) .black := by
  subst hEkw
  have hok := fits_cfgOk hf
  obtain ⟨hkw64, hkb64, hcheb12⟩ := hok
  obtain ⟨hpwb, hpbb, hsym⟩ := fits_kings hf
  have hA := hf.1
  have hkb2 : toSq c.kb = kingSq p .black :=
    Fin.ext (by rw [toSq_val_of_lt c.kb hkb64]; exact (congrArg Cfg.kb hf.2.2).symm)
  have hpbu : ∀ s : Sq, p.board s = some ⟨.black, .king⟩ → s = toSq c.kb :=
    fun s hs => ((kingSq_spec p .black (hA.kings .black)).2 s hs).trans hkb2.symm
  have hkbne : c.kb ≠ c.kw := by
    intro e
    rw [e, cheb_self] at hcheb12
    omega
  refine (eval_att hf hg hl F hF false c.kb hkb64 [c.kw] [] []
    (fun t => if t = toSq c.kw then none else p.board t) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  · refine ⟨?_, ?_, ?_⟩
    · intro q hq hqE _ _
      show (if toSq q = toSq c.kw then none else p.board (toSq q)) = p.board (toSq q)
      rw [if_neg (fun e => hqE (List.mem_singleton.mpr (toSq_inj_of_lt hq hkw64 e)))]
    · intro q hqE _
      rw [List.mem_singleton] at hqE
      show (if toSq q = toSq c.kw then none else p.board (toSq q)) = none
      rw [if_pos (congrArg toSq hqE)]
    · intro q hq
      simp at hq
  · intro q hq
    simp at hq
  · intro q hq h2
    simp at h2
  · intro q hq
    rw [List.mem_singleton] at hq
    rw [hq]
    exact hkw64
  · intro q hq
    simp at hq
  · intro t
    show ((if t = toSq c.kw then none else p.board t) = some ⟨.black, .king⟩) ↔ t = toSq c.kb
    by_cases htk : t = toSq c.kw
    · rw [if_pos htk]
      exact ⟨fun hb => by simp at hb,
        fun hb => absurd (toSq_inj_of_lt hkw64 hkb64 (htk ▸ hb)) (fun e => hkbne e.symm)⟩
    · rw [if_neg htk]
      exact ⟨hpbu t, fun hb => hb ▸ hpbb⟩
  · intro _ hm
    simp at hm
  · intro hm
    rw [List.append_nil, List.mem_singleton] at hm
    exact hkbne hm
  · intro hm
    simp at hm
  · rw [Bool.eq_iff_iff, attacked_iff, decide_eq_true_iff]
    constructor
    · rintro ⟨t, -, pc, hpc, hcol, hatt⟩
      exact ⟨t, pc, hpc, hcol, hatt⟩
    · rintro ⟨t, pc, hpc, hcol, hatt⟩
      exact ⟨t, by simp, pc, hpc, hcol, hatt⟩

theorem king_legal (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (m : Cand) (hm : m ∈ c.kingCands) :
    m.legal.eval A = decide (m.mv ∈ legalMoves p) := by
  obtain ⟨hkw64, hkb64, hcheb12⟩ := fits_cfgOk hf
  obtain ⟨t, ht, hc1, hc2, hmt⟩ := kingCands_unpack hm
  subst hmt
  obtain ⟨hpb, hlocW, hlocB, hsw, hsb⟩ := king_play_facts hf t ht hc1 hc2
  have hturn : p.turn = .white := hf.2.1
  have ht_ne : t ≠ c.kw := by
    intro e
    rw [e, cheb_self] at hc1
    exact absurd hc1 (by decide)
  have htkw2 : toSq t ≠ toSq c.kw := fun e => ht_ne (toSq_inj_of_lt ht hkw64 e)
  have hkbnt : c.kb ≠ t := by
    intro e
    rw [e, cheb_self] at hc2
    exact absurd hc2 (by omega)
  have hkbnkw : c.kb ≠ c.kw := by
    intro e
    rw [e, cheb_self] at hcheb12
    exact absurd hcheb12 (by omega)
  show (Ex.and [Ex.not (c.wocc t), Ex.not (c.attB t [c.kw] [] [t])]).eval A =
    decide (⟨toSq c.kw, toSq t, none⟩ ∈ legalMoves p)
  rw [eval_and2]
  have hpsE : (Ex.not (c.wocc t)).eval A = !(p.board (toSq t)).any (·.color == .white) :=
    congrArg Bool.not (eval_wocc hf hg hl t ht)
  have hAttB : (c.attB t [c.kw] [] [t]).eval A =
      attacked (play p ⟨toSq c.kw, toSq t, none⟩).board (toSq t) .black := by
    have hag : Agrees p (play p ⟨toSq c.kw, toSq t, none⟩).board [c.kw] [] [t] := by
      refine ⟨?_, ?_, ?_⟩
      · intro q hq hqkw _ hqt
        rw [hpb, if_neg (fun e => hqt (List.mem_singleton.mpr (toSq_inj_of_lt hq ht e))),
          if_neg (fun e => hqkw (List.mem_singleton.mpr (toSq_inj_of_lt hq hkw64 e)))]
      · intro q hq _
        rw [List.mem_singleton] at hq
        subst hq
        rw [hpb, if_neg (fun e => ht_ne (toSq_inj_of_lt hkw64 ht e).symm), if_pos rfl]
      · intro q hq
        simp at hq
    refine (eval_att hf hg hl t ht false c.kb hkb64 [c.kw] [] [t]
      (play p ⟨toSq c.kw, toSq t, none⟩).board hag
      (fun q hq => Or.inr (List.mem_singleton.mp hq))
      (fun q _ h2 => by simp at h2)
      (fun q hq => List.mem_singleton.mp hq ▸ hkw64)
      (fun q hq => by simp at hq)
      (fun t' => hlocB t')
      (fun _ hm2 => absurd (List.mem_singleton.mp hm2) hkbnt)
      (fun hm2 => hkbnkw (List.mem_singleton.mp (by rwa [List.append_nil] at hm2)))
      (fun hm2 => by simp at hm2)).trans ?_
    rw [Bool.eq_iff_iff, attacked_iff, decide_eq_true_iff]
    constructor
    · rintro ⟨t', ht', pc, hpc, hcol, hatt⟩
      exact ⟨t', pc, hpc, hcol, hatt⟩
    · rintro ⟨t', pc, hpc, hcol, hatt⟩
      refine ⟨t', ?_, pc, hpc, hcol, hatt⟩
      intro hmem
      have hm2 := List.mem_singleton.mp hmem
      have htE : t' = toSq t := by
        have h1 := toSq_val t'
        rw [hm2] at h1
        exact h1.symm
      subst htE
      rw [hsw] at hpc
      obtain rfl := Option.some.inj hpc
      exact absurd hcol (by decide)
  have hAttB2 : (Ex.not (c.attB t [c.kw] [] [t])).eval A =
      (!attacked (play p ⟨toSq c.kw, toSq t, none⟩).board (toSq t) .black) :=
    congrArg Bool.not hAttB
  rw [hpsE, hAttB2]
  have hInc : inCheck (play p ⟨toSq c.kw, toSq t, none⟩) p.turn =
      attacked (play p ⟨toSq c.kw, toSq t, none⟩).board (toSq t) .black := by
    rw [hturn]
    unfold inCheck
    exact inCheck_eq_of_uniq hsw (fun s hs => (hlocW s).mp hs)
  have hchebd : dist (toSq c.kw) (toSq t) = 1 := by
    rw [← cheb_toSq c.kw t hkw64 ht]
    exact hc1
  have hPs : (⟨toSq c.kw, toSq t, none⟩ : Move) ∈ pseudo p ↔
      (p.board (toSq t)).any (·.color == .white) = false := by
    obtain ⟨hpwb, -, -⟩ := fits_kings hf
    constructor
    · intro hps
      rcases pseudo_cases hps with ⟨s', q', hbs, hcol, hpm⟩ | hcm
      · have hsrc := move_src_of_pieceMoves hpm
        have hsq' : s' = toSq c.kw := hsrc.symm
        subst hsq'
        rw [hpwb] at hbs
        obtain rfl := Option.some.inj hbs
        rcases pieceMoves_cases hpm with ⟨hkp, -⟩ | ⟨-, -, hpn, hdst⟩
        · exact absurd hkp (by decide)
        · have h2 := (List.mem_filter.mp hdst).2
          rwa [Bool.not_eq_true'] at h2
      · obtain ⟨hsrc2, hpn2, hbK2, hs4, hside2⟩ := castleMoves_cases hcm
        exfalso
        have h2 : dist (⟨toSq c.kw, toSq t, none⟩ : Move).src (⟨toSq c.kw, toSq t, none⟩ : Move).dst = 1 :=
          hchebd
        rcases hside2 with ⟨hdst, -, -, -, -⟩ | ⟨hdst, -, -, -, -, -⟩
        · rw [hsrc2, hdst, hturn] at h2
          have h3 : dist (sq 4 Color.white.home) (sq 6 Color.white.home) = 2 := by decide
          rw [h3] at h2
          exact absurd h2 (by decide)
        · rw [hsrc2, hdst, hturn] at h2
          have h3 : dist (sq 4 Color.white.home) (sq 2 Color.white.home) = 2 := by decide
          rw [h3] at h2
          exact absurd h2 (by decide)
    · intro hwoc
      refine mem_pseudo_of p (toSq c.kw) ⟨.white, .king⟩ ⟨toSq c.kw, toSq t, none⟩ hpwb
        hturn.symm (mem_pieceMoves_of_attacks p (toSq c.kw) ⟨.white, .king⟩ (by decide) (toSq t) ?_ hwoc)
      exact (mem_attacks_king p.board (toSq c.kw) (toSq t) .white).mpr (by
        rw [toSq_val_of_lt c.kw hkw64, toSq_val_of_lt t ht]
        exact hc1)
  rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', decide_eq_true_iff]
  constructor
  · rintro ⟨hwo, hatt⟩
    unfold legalMoves
    rw [List.mem_filter]
    exact ⟨hPs.mpr hwo, by rw [Bool.not_eq_true', hInc]; exact hatt⟩
  · intro hlg
    obtain ⟨hpsm, hic⟩ := mem_legalMoves hlg
    exact ⟨hPs.mp hpsm, hInc ▸ hic⟩

theorem king_chk (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (m : Cand) (hm : m ∈ c.kingCands)
    (h : m.mv ∈ legalMoves p) : m.chk.eval A = givesCheck p m.mv := by
  obtain ⟨hkw64, hkb64, hcheb12⟩ := fits_cfgOk hf
  obtain ⟨t, ht, hc1, hc2, hmt⟩ := kingCands_unpack hm
  subst hmt
  obtain ⟨hpb, hlocW, hlocB, hsw, hsb⟩ := king_play_facts hf t ht hc1 hc2
  have hturn : p.turn = .white := hf.2.1
  have ht_ne : t ≠ c.kw := by
    intro e
    rw [e, cheb_self] at hc1
    exact absurd hc1 (by decide)
  have hkbnt : c.kb ≠ t := by
    intro e
    rw [e, cheb_self] at hc2
    exact absurd hc2 (by omega)
  have hkbnkw : c.kb ≠ c.kw := by
    intro e
    rw [e, cheb_self] at hcheb12
    exact absurd hcheb12 (by omega)
  show (c.attW c.kb [c.kw] [t] [t] t).eval A = givesCheck p ⟨toSq c.kw, toSq t, none⟩
  have hAttW : (c.attW c.kb [c.kw] [t] [t] t).eval A =
      attacked (play p ⟨toSq c.kw, toSq t, none⟩).board (toSq c.kb) .white := by
    have hag : Agrees p (play p ⟨toSq c.kw, toSq t, none⟩).board [c.kw] [t] [t] := by
      refine ⟨?_, ?_, ?_⟩
      · intro q hq hqkw hqt _
        rw [hpb, if_neg (fun e => hqt (List.mem_singleton.mpr (toSq_inj_of_lt hq ht e))),
          if_neg (fun e => hqkw (List.mem_singleton.mpr (toSq_inj_of_lt hq hkw64 e)))]
      · intro q hq _
        rw [List.mem_singleton] at hq
        subst hq
        rw [hpb, if_neg (fun e => ht_ne (toSq_inj_of_lt hkw64 ht e).symm), if_pos rfl]
      · intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        rw [hsw]
        exact Option.some_ne_none _
    refine (eval_att hf hg hl c.kb hkb64 true t ht [c.kw] [t] [t]
      (play p ⟨toSq c.kw, toSq t, none⟩).board hag
      (fun q hq => Or.inl hq)
      (fun q hq h2 => absurd ((List.mem_singleton.mp hq).symm.trans (List.mem_singleton.mp h2))
        (fun e => ht_ne e.symm))
      (fun q hq => List.mem_singleton.mp hq ▸ hkw64)
      (fun q hq => List.mem_singleton.mp hq ▸ ht)
      (fun t' => hlocW t')
      (fun h1 _ => absurd h1 (by rw [cheb_symm]; omega))
      (fun hm2 => by
        rw [List.mem_append, List.mem_singleton, List.mem_singleton] at hm2
        rcases hm2 with hm2 | hm2
        · exact hkbnkw hm2
        · exact hkbnt hm2)
      (fun hm2 => ht_ne (List.mem_singleton.mp hm2).symm)).trans ?_
    rw [Bool.eq_iff_iff, attacked_iff, decide_eq_true_iff]
    constructor
    · rintro ⟨t', -, pc, hpc, hcol, hatt⟩
      exact ⟨t', pc, hpc, hcol, hatt⟩
    · rintro ⟨t', pc, hpc, hcol, hatt⟩
      refine ⟨t', ?_, pc, hpc, hcol, hatt⟩
      intro hmem
      simp only [List.mem_append, List.mem_singleton, or_self] at hmem
      have htE : t' = toSq t := by
        have h1 := toSq_val t'
        rw [hmem] at h1
        exact h1.symm
      subst htE
      rw [hsw] at hpc
      obtain rfl := Option.some.inj hpc
      have h2 := (mem_attacks_king (play p ⟨toSq c.kw, toSq t, none⟩).board (toSq t) (toSq c.kb)
        .white).mp hatt
      rw [toSq_val_of_lt t ht, toSq_val_of_lt c.kb hkb64, cheb_symm] at h2
      omega
  rw [hAttW]
  have hgc : givesCheck p ⟨toSq c.kw, toSq t, none⟩ =
      attacked (play p ⟨toSq c.kw, toSq t, none⟩).board (toSq c.kb) .white := by
    show inCheck (play p ⟨toSq c.kw, toSq t, none⟩) p.turn.opp = _
    rw [hturn]
    unfold inCheck
    exact inCheck_eq_of_uniq hsb (fun s hs => (hlocB s).mp hs)
  rw [hgc]

theorem tsq0 : toSq A1 = sq 0 Color.white.home := by decide

theorem tsq1 : toSq B1 = sq 1 Color.white.home := by decide

theorem tsq2 : toSq C1 = sq 2 Color.white.home := by decide

theorem tsq3 : toSq D1 = sq 3 Color.white.home := by decide

theorem tsq4 : toSq E1 = sq 4 Color.white.home := by decide

theorem tsq5 : toSq F1 = sq 5 Color.white.home := by decide

theorem tsq6 : toSq G1 = sq 6 Color.white.home := by decide

theorem tsq7 : toSq H1 = sq 7 Color.white.home := by decide

theorem empty_true_iff_none (b : Board) (s : Sq) : empty b s = true ↔ b s = none :=
  Option.isNone_iff_eq_none

theorem mem_pseudo_of_castle {p : Pos} {mv : Move} (h : mv ∈ castleMoves p) : mv ∈ pseudo p := by
  show mv ∈ allSq.flatMap (fun s => match p.board s with
      | some q => if q.color == p.turn then pieceMoves p s q else [] | none => []) ++ castleMoves p
  exact List.mem_append.mpr (Or.inr h)

theorem eval_v_cr (hg : Good p A s) (hr : RightsOk c s r) (b : Bool) (v : Int)
    (hlk : r.cr.lookup b = some v) :
    (Ex.v v).eval A = (if b then p.castleK .white else p.castleQ .white) := by
  obtain ⟨hv0, hd⟩ := hr.2.2.1 b v (mem_of_lookup_eq_some r.cr hlk)
  obtain ⟨hi, hd2⟩ := Array.getElem?_eq_some_iff.mp hd
  have hA : A ((v.toNat - 1) + 1) = (s.defs[v.toNat - 1]).val p A := hg _ hi
  rw [hd2] at hA
  show (if 0 < v then A v.toNat else !A v.natAbs) = if b then p.castleK .white else p.castleQ .white
  rw [if_pos hv0]
  have hvt : v.toNat - 1 + 1 = v.toNat := by omega
  rw [← hvt]
  exact hA

theorem castleMoves_iff_K (p : Pos) (hturn : p.turn = .white) :
    (⟨toSq E1, toSq G1, none⟩ : Move) ∈ castleMoves p ↔
      (p.board (toSq E1) = some ⟨.white, .king⟩ ∧ attacked p.board (toSq E1) .black = false ∧
        p.castleK .white = true ∧ p.board (toSq H1) = some ⟨.white, .rook⟩ ∧
        p.board (toSq F1) = none ∧ p.board (toSq G1) = none ∧
        attacked p.board (toSq F1) .black = false) := by
  constructor
  · intro h
    unfold castleMoves at h
    dsimp only at h
    split at h
    · next hE =>
      rw [Bool.and_eq_true, beq_iff_eq] at hE
      obtain ⟨hE1, hE2⟩ := hE
      rcases List.mem_append.mp h with hK | hQ
      · split at hK
        · next hcond =>
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcond
          obtain ⟨⟨⟨hcK, hr7⟩, hfree⟩, hs5t⟩ := hcond
          rw [beq_iff_eq] at hr7
          have h5 : empty p.board (sq 5 p.turn.home) = true := List.all_eq_true.mp hfree 5 (by simp)
          have h6 : empty p.board (sq 6 p.turn.home) = true := List.all_eq_true.mp hfree 6 (by simp)
          rw [hturn] at hE1 hE2 hcK hr7 h5 h6 hs5t
          refine ⟨tsq4.symm ▸ hE1, tsq4.symm ▸ Bool.not_eq_true' _ ▸ hE2, hcK, tsq7.symm ▸ hr7,
            ?_, ?_, ?_⟩
          · exact (empty_true_iff_none _ _).mp (tsq5.symm ▸ h5)
          · exact (empty_true_iff_none _ _).mp (tsq6.symm ▸ h6)
          · exact tsq5.symm ▸ Bool.not_eq_true' _ ▸ hs5t
        · simp at hK
      · split at hQ
        · next hcond =>
          have h2 := List.mem_singleton.mp hQ
          rw [hturn] at h2
          have h3 : toSq G1 = sq 2 Color.white.home := congrArg Move.dst h2
          exact absurd (congrArg Fin.val h3) (by decide)
        · simp at hQ
    · simp at h
  · rintro ⟨hb4K, hs4, hck, hr7, h5, h6, hs5⟩
    unfold castleMoves
    dsimp only
    rw [hturn]
    rw [if_pos (by
      rw [Bool.and_eq_true, beq_iff_eq]
      exact ⟨tsq4 ▸ hb4K, (Bool.not_eq_true' _).symm ▸
        (show attacked p.board (sq 4 Color.white.home) .black = false from tsq4 ▸ hs4)⟩)]
    refine List.mem_append.mpr (Or.inl ?_)
    rw [if_pos (by
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨hck, tsq7 ▸ hr7⟩, ?_⟩, ?_⟩
      · show (empty p.board (sq 5 Color.white.home) && (empty p.board (sq 6 Color.white.home) &&
          true)) = true
        rw [show empty p.board (sq 5 Color.white.home) = true from
          (empty_true_iff_none _ _).mpr (tsq5 ▸ h5),
          show empty p.board (sq 6 Color.white.home) = true from
          (empty_true_iff_none _ _).mpr (tsq6 ▸ h6)]
        rfl
      · exact (Bool.not_eq_true' _).symm ▸ (tsq5 ▸ hs5))]
    exact List.mem_singleton.mpr rfl

theorem castleMoves_iff_Q (p : Pos) (hturn : p.turn = .white) :
    (⟨toSq E1, toSq C1, none⟩ : Move) ∈ castleMoves p ↔
      (p.board (toSq E1) = some ⟨.white, .king⟩ ∧ attacked p.board (toSq E1) .black = false ∧
        p.castleQ .white = true ∧ p.board (toSq A1) = some ⟨.white, .rook⟩ ∧
        p.board (toSq B1) = none ∧ p.board (toSq C1) = none ∧ p.board (toSq D1) = none ∧
        attacked p.board (toSq D1) .black = false) := by
  constructor
  · intro h
    unfold castleMoves at h
    dsimp only at h
    split at h
    · next hE =>
      rw [Bool.and_eq_true, beq_iff_eq] at hE
      obtain ⟨hE1, hE2⟩ := hE
      rcases List.mem_append.mp h with hK | hQ
      · split at hK
        · next hcond =>
          have h2 := List.mem_singleton.mp hK
          rw [hturn] at h2
          have h3 : toSq C1 = sq 6 Color.white.home := congrArg Move.dst h2
          exact absurd (congrArg Fin.val h3) (by decide)
        · simp at hK
      · split at hQ
        · next hcond =>
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcond
          obtain ⟨⟨⟨hcQ, hr0⟩, hfree⟩, hs3t⟩ := hcond
          rw [beq_iff_eq] at hr0
          have h1 : empty p.board (sq 1 p.turn.home) = true := List.all_eq_true.mp hfree 1 (by simp)
          have h2 : empty p.board (sq 2 p.turn.home) = true := List.all_eq_true.mp hfree 2 (by simp)
          have h3 : empty p.board (sq 3 p.turn.home) = true := List.all_eq_true.mp hfree 3 (by simp)
          rw [hturn] at hE1 hE2 hcQ hr0 h1 h2 h3 hs3t
          refine ⟨tsq4.symm ▸ hE1, tsq4.symm ▸ Bool.not_eq_true' _ ▸ hE2, hcQ, tsq0.symm ▸ hr0,
            ?_, ?_, ?_, ?_⟩
          · exact (empty_true_iff_none _ _).mp (tsq1.symm ▸ h1)
          · exact (empty_true_iff_none _ _).mp (tsq2.symm ▸ h2)
          · exact (empty_true_iff_none _ _).mp (tsq3.symm ▸ h3)
          · exact tsq3.symm ▸ Bool.not_eq_true' _ ▸ hs3t
        · simp at hQ
    · simp at h
  · rintro ⟨hb4K, hs4, hck, hr0, h1, h2, h3, hs3⟩
    unfold castleMoves
    dsimp only
    rw [hturn]
    rw [if_pos (by
      rw [Bool.and_eq_true, beq_iff_eq]
      exact ⟨tsq4 ▸ hb4K, (Bool.not_eq_true' _).symm ▸
        (show attacked p.board (sq 4 Color.white.home) .black = false from tsq4 ▸ hs4)⟩)]
    refine List.mem_append.mpr (Or.inr ?_)
    rw [if_pos (by
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨hck, tsq0 ▸ hr0⟩, ?_⟩, ?_⟩
      · show (empty p.board (sq 1 Color.white.home) && (empty p.board (sq 2 Color.white.home) &&
          (empty p.board (sq 3 Color.white.home) && true))) = true
        rw [show empty p.board (sq 1 Color.white.home) = true from
          (empty_true_iff_none _ _).mpr (tsq1 ▸ h1),
          show empty p.board (sq 2 Color.white.home) = true from
          (empty_true_iff_none _ _).mpr (tsq2 ▸ h2),
          show empty p.board (sq 3 Color.white.home) = true from
          (empty_true_iff_none _ _).mpr (tsq3 ▸ h3)]
        rfl
      · exact (Bool.not_eq_true' _).symm ▸ (tsq3 ▸ hs3))]
    exact List.mem_singleton.mpr rfl

theorem castleK_mv_not_piece (p : Pos) (hpb4 : p.board (toSq E1) = some ⟨.white, .king⟩)
    {s' : Sq} {q' : Piece} (hbs : p.board s' = some q')
    (hpm : (⟨toSq E1, toSq G1, none⟩ : Move) ∈ pieceMoves p s' q') : False := by
  have hsrc := move_src_of_pieceMoves hpm
  have hsq' : s' = toSq E1 := hsrc.symm
  subst hsq'
  rw [hpb4] at hbs
  obtain rfl := Option.some.inj hbs
  rcases pieceMoves_cases hpm with ⟨hkp, -⟩ | ⟨-, -, hpn, hdst⟩
  · exact absurd hkp (by decide)
  · have h1 := (List.mem_filter.mp hdst).1
    have h2 := (mem_attacks_king p.board (toSq E1) (toSq G1) .white).mp (show toSq G1 ∈ attacks p.board
        (toSq E1) ⟨.white, .king⟩ from h1)
    rw [toSq_val_of_lt E1 (by decide), toSq_val_of_lt G1 (by decide)] at h2
    have h3 : cheb E1 G1 = 2 := by decide
    omega

theorem castleQ_mv_not_piece (p : Pos) (hpb4 : p.board (toSq E1) = some ⟨.white, .king⟩)
    {s' : Sq} {q' : Piece} (hbs : p.board s' = some q')
    (hpm : (⟨toSq E1, toSq C1, none⟩ : Move) ∈ pieceMoves p s' q') : False := by
  have hsrc := move_src_of_pieceMoves hpm
  have hsq' : s' = toSq E1 := hsrc.symm
  subst hsq'
  rw [hpb4] at hbs
  obtain rfl := Option.some.inj hbs
  rcases pieceMoves_cases hpm with ⟨hkp, -⟩ | ⟨-, -, hpn, hdst⟩
  · exact absurd hkp (by decide)
  · have h1 := (List.mem_filter.mp hdst).1
    have h2 := (mem_attacks_king p.board (toSq E1) (toSq C1) .white).mp (show toSq C1 ∈ attacks p.board
        (toSq E1) ⟨.white, .king⟩ from h1)
    rw [toSq_val_of_lt E1 (by decide), toSq_val_of_lt C1 (by decide)] at h2
    have h3 : cheb E1 C1 = 2 := by decide
    omega

theorem castleK_play_facts (hf : Fits c p) (hkwe : c.kw = E1) :
    (∀ s : Sq, (play p ⟨toSq E1, toSq G1, none⟩).board s =
        if s = toSq G1 then some ⟨.white, .king⟩
        else if s = toSq E1 then none
        else if s = toSq F1 then p.board (toSq H1)
        else if s = toSq H1 then none else p.board s)
    ∧ (∀ s : Sq, (play p ⟨toSq E1, toSq G1, none⟩).board s = some ⟨.white, .king⟩ ↔ s = toSq G1)
    ∧ (play p ⟨toSq E1, toSq G1, none⟩).board (toSq G1) = some ⟨.white, .king⟩ := by
  obtain ⟨hkw64, hkb64, hcheb12⟩ := fits_cfgOk hf
  obtain ⟨hpwb, hpbb, hsym⟩ := fits_kings hf
  have hA := hf.1
  have hkw2 : toSq c.kw = kingSq p .white :=
    Fin.ext (by rw [toSq_val_of_lt c.kw hkw64]; exact (congrArg Cfg.kw hf.2.2).symm)
  have hpwu' : ∀ s, p.board s = some ⟨.white, .king⟩ → s = toSq c.kw :=
    fun s hs => ((kingSq_spec p .white (hA.kings .white)).2 s hs).trans hkw2.symm
  have hpb4 : p.board (toSq E1) = some ⟨.white, .king⟩ := hkwe ▸ hpwb
  have hcastK : isCastle p ⟨toSq E1, toSq G1, none⟩ = true := by
    show ((p.board (toSq E1)).any (·.kind == .king) &&
      ((toSq E1).file + 2 == (toSq G1).file || (toSq G1).file + 2 == (toSq E1).file)) = true
    rw [show (p.board (toSq E1)).any (·.kind == .king) = true from by rw [hpb4]; rfl]
    rw [show ((toSq E1).file + 2 == (toSq G1).file || (toSq G1).file + 2 == (toSq E1).file) = true
      from by decide]
    rfl
  have hmf : moved p ⟨toSq E1, toSq G1, none⟩ = some ⟨.white, .king⟩ := hpb4
  have hrf : rookFrom ⟨toSq E1, toSq G1, none⟩ = toSq H1 := by decide
  have hrt : rookTo ⟨toSq E1, toSq G1, none⟩ = toSq F1 := by decide
  have hpb : ∀ s : Sq, (play p ⟨toSq E1, toSq G1, none⟩).board s =
      if s = toSq G1 then some ⟨.white, .king⟩
      else if s = toSq E1 then none
      else if s = toSq F1 then p.board (toSq H1)
      else if s = toSq H1 then none else p.board s := by
    intro s
    rw [play_board_castle p ⟨toSq E1, toSq G1, none⟩ hcastK s]
    show (if s = toSq G1 then moved p ⟨toSq E1, toSq G1, none⟩
        else if s = toSq E1 then none
        else if s = rookTo ⟨toSq E1, toSq G1, none⟩ then p.board (rookFrom ⟨toSq E1, toSq G1, none⟩)
        else if s = rookFrom ⟨toSq E1, toSq G1, none⟩ then none else p.board s) = _
    rw [hmf, hrt, hrf]
  have hswG : (play p ⟨toSq E1, toSq G1, none⟩).board (toSq G1) = some ⟨.white, .king⟩ := by
    rw [hpb (toSq G1), if_pos rfl]
  refine ⟨hpb, ?_, hswG⟩
  intro s
  rw [hpb s]
  by_cases h1 : s = toSq G1
  · rw [if_pos h1]
    exact ⟨fun _ => h1, fun _ => rfl⟩
  · rw [if_neg h1]
    by_cases h2 : s = toSq E1
    · rw [if_pos h2]
      exact ⟨fun hh => by simp at hh, fun hh => absurd hh h1⟩
    · rw [if_neg h2]
      by_cases h3 : s = toSq F1
      · rw [if_pos h3]
        constructor
        · intro hh
          have e := hpwu' (toSq H1) hh
          have e2 := toSq_inj_of_lt (by decide : H1 < 64) hkw64 e
          exact absurd (e2.trans hkwe) (by decide)
        · intro hh
          exact absurd (toSq_inj_of_lt (by decide : F1 < 64) (by decide : G1 < 64) (h3 ▸ hh))
            (by decide)
      · rw [if_neg h3]
        by_cases h4 : s = toSq H1
        · rw [if_pos h4]
          exact ⟨fun hh => by simp at hh, fun hh => absurd hh h1⟩
        · rw [if_neg h4]
          exact ⟨fun hh => absurd ((hpwu' s hh).trans (congrArg toSq hkwe)) h2, fun hh =>
            absurd hh h1⟩

theorem castleQ_play_facts (hf : Fits c p) (hkwe : c.kw = E1) :
    (∀ s : Sq, (play p ⟨toSq E1, toSq C1, none⟩).board s =
        if s = toSq C1 then some ⟨.white, .king⟩
        else if s = toSq E1 then none
        else if s = toSq D1 then p.board (toSq A1)
        else if s = toSq A1 then none else p.board s)
    ∧ (∀ s : Sq, (play p ⟨toSq E1, toSq C1, none⟩).board s = some ⟨.white, .king⟩ ↔ s = toSq C1)
    ∧ (play p ⟨toSq E1, toSq C1, none⟩).board (toSq C1) = some ⟨.white, .king⟩ := by
  obtain ⟨hkw64, hkb64, hcheb12⟩ := fits_cfgOk hf
  obtain ⟨hpwb, hpbb, hsym⟩ := fits_kings hf
  have hA := hf.1
  have hkw2 : toSq c.kw = kingSq p .white :=
    Fin.ext (by rw [toSq_val_of_lt c.kw hkw64]; exact (congrArg Cfg.kw hf.2.2).symm)
  have hpwu' : ∀ s, p.board s = some ⟨.white, .king⟩ → s = toSq c.kw :=
    fun s hs => ((kingSq_spec p .white (hA.kings .white)).2 s hs).trans hkw2.symm
  have hpb4 : p.board (toSq E1) = some ⟨.white, .king⟩ := hkwe ▸ hpwb
  have hcastQ : isCastle p ⟨toSq E1, toSq C1, none⟩ = true := by
    show ((p.board (toSq E1)).any (·.kind == .king) &&
      ((toSq E1).file + 2 == (toSq C1).file || (toSq C1).file + 2 == (toSq E1).file)) = true
    rw [show (p.board (toSq E1)).any (·.kind == .king) = true from by rw [hpb4]; rfl]
    rw [show ((toSq E1).file + 2 == (toSq C1).file || (toSq C1).file + 2 == (toSq E1).file) = true
      from by decide]
    rfl
  have hmf : moved p ⟨toSq E1, toSq C1, none⟩ = some ⟨.white, .king⟩ := hpb4
  have hrf : rookFrom ⟨toSq E1, toSq C1, none⟩ = toSq A1 := by decide
  have hrt : rookTo ⟨toSq E1, toSq C1, none⟩ = toSq D1 := by decide
  have hpb : ∀ s : Sq, (play p ⟨toSq E1, toSq C1, none⟩).board s =
      if s = toSq C1 then some ⟨.white, .king⟩
      else if s = toSq E1 then none
      else if s = toSq D1 then p.board (toSq A1)
      else if s = toSq A1 then none else p.board s := by
    intro s
    rw [play_board_castle p ⟨toSq E1, toSq C1, none⟩ hcastQ s]
    show (if s = toSq C1 then moved p ⟨toSq E1, toSq C1, none⟩
        else if s = toSq E1 then none
        else if s = rookTo ⟨toSq E1, toSq C1, none⟩ then p.board (rookFrom ⟨toSq E1, toSq C1, none⟩)
        else if s = rookFrom ⟨toSq E1, toSq C1, none⟩ then none else p.board s) = _
    rw [hmf, hrt, hrf]
  have hswC : (play p ⟨toSq E1, toSq C1, none⟩).board (toSq C1) = some ⟨.white, .king⟩ := by
    rw [hpb (toSq C1), if_pos rfl]
  refine ⟨hpb, ?_, hswC⟩
  intro s
  rw [hpb s]
  by_cases h1 : s = toSq C1
  · rw [if_pos h1]
    exact ⟨fun _ => h1, fun _ => rfl⟩
  · rw [if_neg h1]
    by_cases h2 : s = toSq E1
    · rw [if_pos h2]
      exact ⟨fun hh => by simp at hh, fun hh => absurd hh h1⟩
    · rw [if_neg h2]
      by_cases h3 : s = toSq D1
      · rw [if_pos h3]
        constructor
        · intro hh
          have e := hpwu' (toSq A1) hh
          have e2 := toSq_inj_of_lt (by decide : A1 < 64) hkw64 e
          exact absurd (e2.trans hkwe) (by decide)
        · intro hh
          exact absurd (toSq_inj_of_lt (by decide : D1 < 64) (by decide : C1 < 64) (h3 ▸ hh))
            (by decide)
      · rw [if_neg h3]
        by_cases h4 : s = toSq A1
        · rw [if_pos h4]
          exact ⟨fun hh => by simp at hh, fun hh => absurd hh h1⟩
        · rw [if_neg h4]
          exact ⟨fun hh => absurd ((hpwu' s hh).trans (congrArg toSq hkwe)) h2, fun hh =>
            absurd hh h1⟩

def setAt (b : Board) (s : Sq) (o : Option Piece) : Board := fun x => if x = s then o else b x

theorem setAt_eq (b : Board) (s : Sq) (o : Option Piece) (x : Sq) :
    setAt b s o x = (if x = s then o else b x) := rfl

theorem eval_attB_play (hf : Fits c p) (hg : Good p A s) (hl : Layout c s)
    (G R1 R2 R3 : Nat) (mv : Move)
    (hG : G < 64) (hR1 : R1 < 64) (hR2 : R2 < 64) (hR3 : R3 < 64)
    (hd12 : R1 ≠ R2) (hd13 : R1 ≠ R3) (hd23 : R2 ≠ R3)
    (hd1G : R1 ≠ G) (hd2G : R2 ≠ G) (hd3G : R3 ≠ G)
    (hn1 : (play p mv).board (toSq R1) = none) (hn2 : (play p mv).board (toSq R2) = none)
    (ho3 : (play p mv).board (toSq R3) = some ⟨.white, .rook⟩)
    (hb4 : ∀ q < 64, q ≠ R1 → q ≠ R2 → q ≠ R3 → q ≠ G →
      (play p mv).board (toSq q) = p.board (toSq q))
    (hkb1 : c.kb ≠ R1) (hkb2n : c.kb ≠ R2) (hkb3n : c.kb ≠ R3)
    (hkw3 : c.kw ≠ R3) :
    (c.attB G [R1, R2] [R3] []).eval A =
      attacked (play p mv).board (toSq G) .black := by
  obtain ⟨hkw64, hkb64, hcheb12⟩ := fits_cfgOk hf
  obtain ⟨hpwb, hpbb, hsym⟩ := fits_kings hf
  have hA := hf.1
  have hkb2 : toSq c.kb = kingSq p .black :=
    Fin.ext (by rw [toSq_val_of_lt c.kb hkb64]; exact (congrArg Cfg.kb hf.2.2).symm)
  have hpbu : ∀ s : Sq, p.board s = some ⟨.black, .king⟩ → s = toSq c.kb :=
    fun s hs => ((kingSq_spec p .black (hA.kings .black)).2 s hs).trans hkb2.symm
  have hag : Agrees p (setAt (play p mv).board (toSq G) (p.board (toSq G))) [R1, R2] [R3] [] := by
    refine ⟨?_, ?_, ?_⟩
    · intro q hq hq12 hq3 _
      rw [setAt_eq]
      by_cases hqG : q = G
      · rw [if_pos (congrArg toSq hqG), hqG]
      · rw [if_neg (fun e => hqG (toSq_inj_of_lt hq hG e))]
        exact hb4 q hq (fun e => hq12 (List.mem_cons.mpr (Or.inl e)))
          (fun e => hq12 (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr e))))
          (fun e => hq3 (List.mem_singleton.mpr e)) hqG
    · intro q hq12 hq3
      rw [List.mem_cons, List.mem_singleton] at hq12
      rcases hq12 with hq12 | hq12
      · subst hq12
        rw [setAt_eq, if_neg (fun e => hd1G (toSq_inj_of_lt hR1 hG e)), hn1]
      · subst hq12
        rw [setAt_eq, if_neg (fun e => hd2G (toSq_inj_of_lt hR2 hG e)), hn2]
    · intro q hq3
      rw [List.mem_singleton] at hq3
      subst hq3
      rw [setAt_eq, if_neg (fun e => hd3G (toSq_inj_of_lt hR3 hG e)), ho3]
      exact Option.some_ne_none _
  refine (eval_att hf hg hl G hG false c.kb hkb64 [R1, R2] [R3] []
    (setAt (play p mv).board (toSq G) (p.board (toSq G))) hag
    (fun q hq => by simp at hq)
    (fun q hq hm2 => by
      rw [List.mem_cons, List.mem_singleton] at hq
      rcases hq with hq | hq
      · exact hd13 (hq.symm.trans (List.mem_singleton.mp hm2))
      · exact hd23 (hq.symm.trans (List.mem_singleton.mp hm2)))
    (fun q hq => by
      rw [List.mem_cons, List.mem_singleton] at hq
      rcases hq with hq | hq
      · exact hq ▸ hR1
      · exact hq ▸ hR2)
    (fun q hq => (List.mem_singleton.mp hq) ▸ hR3)
    ?_ ?_ ?_ ?_).trans ?_
  · intro t
    show (setAt (play p mv).board (toSq G) (p.board (toSq G)) t = some ⟨.black, .king⟩) ↔
      t = toSq c.kb
    rw [setAt_eq]
    by_cases htG : t = toSq G
    · rw [if_pos htG]
      constructor
      · intro hh
        exact htG.trans (hpbu (toSq G) hh)
      · intro hh
        have h2 : c.kb = G := toSq_inj_of_lt hkb64 hG (hh.symm.trans htG)
        exact h2 ▸ hpbb
    · rw [if_neg htG]
      constructor
      · intro hh
        by_cases ht1 : t = toSq R1
        · rw [ht1, hn1] at hh
          simp at hh
        · by_cases ht2 : t = toSq R2
          · rw [ht2, hn2] at hh
            simp at hh
          · by_cases ht3 : t = toSq R3
            · rw [ht3, ho3] at hh
              have h2 := Option.some.inj hh
              simp only [Piece.mk.injEq] at h2
              exact absurd h2.1 (by decide)
            · have he4 : (play p mv).board t = p.board t := by
                have h2 := hb4 t.val t.isLt
                  (fun e => ht1 ((toSq_val t).symm.trans (congrArg toSq e)))
                  (fun e => ht2 ((toSq_val t).symm.trans (congrArg toSq e)))
                  (fun e => ht3 ((toSq_val t).symm.trans (congrArg toSq e)))
                  (fun e => htG ((toSq_val t).symm.trans (congrArg toSq e)))
                rw [toSq_val t] at h2
                exact h2
              exact hpbu t (he4 ▸ hh)
      · intro hh
        subst hh
        have hkbG : c.kb ≠ G := fun e => htG (congrArg toSq e)
        show (play p mv).board (toSq c.kb) = some ⟨.black, .king⟩
        exact (hb4 c.kb hkb64 hkb1 hkb2n hkb3n hkbG).trans hpbb
  · intro _ hm
    simp only [List.append_nil] at hm
    exact hkb3n (List.mem_singleton.mp hm)
  · intro hm
    rw [List.mem_append, List.mem_cons, List.mem_singleton, List.mem_singleton] at hm
    rcases hm with (hm | hm) | hm
    · exact hkb1 hm
    · exact hkb2n hm
    · exact hkb3n hm
  · intro hm
    exact hkw3 (List.mem_singleton.mp hm)
  · rw [show attacked (play p mv).board (toSq G) .black =
        attacked (setAt (play p mv).board (toSq G) (p.board (toSq G))) (toSq G) .black from
        (attacked_congr_off (s := toSq G) fun t ht => by rw [setAt_eq, if_neg ht]).symm]
    rw [Bool.eq_iff_iff, attacked_iff, decide_eq_true_iff]
    constructor
    · rintro ⟨t, -, pc, hpc, hcol, hatt⟩
      exact ⟨t, pc, hpc, hcol, hatt⟩
    · rintro ⟨t, pc, hpc, hcol, hatt⟩
      refine ⟨t, ?_, pc, hpc, hcol, hatt⟩
      intro hmem
      simp only [List.append_nil, List.mem_singleton] at hmem
      have ht3 : t = toSq R3 := by
        have h1 := toSq_val t
        rw [hmem] at h1
        exact h1.symm
      subst ht3
      rw [setAt_eq, if_neg (fun e => hd3G (toSq_inj_of_lt hR3 hG e)), ho3] at hpc
      obtain rfl := Option.some.inj hpc
      exact absurd hcol (by decide)

theorem attSplit2 {b' : Board} {s : Sq} {d₁ d₂ : Nat} {col : Color} {pc₁ pc₂ : Piece}
    (h1 : b' (toSq d₁) = some pc₁) (hc1 : pc₁.color = col)
    (h2 : b' (toSq d₂) = some pc₂) (hc2 : pc₂.color = col) :
    (∃ t pc, b' t = some pc ∧ pc.color = col ∧ s ∈ attacks b' t pc) ↔
      (s ∈ attacks b' (toSq d₁) pc₁) ∨ (s ∈ attacks b' (toSq d₂) pc₂) ∨
        ∃ t : Sq, t.val ∉ [d₁, d₂] ++ [d₁, d₂] ∧ ∃ pc, b' t = some pc ∧ pc.color = col ∧
          s ∈ attacks b' t pc := by
  constructor
  · rintro ⟨t, pc, hb, hc, ha⟩
    by_cases ht1 : t = toSq d₁
    · subst ht1
      rw [h1] at hb
      obtain rfl := Option.some.inj hb
      exact Or.inl ha
    · by_cases ht2 : t = toSq d₂
      · subst ht2
        rw [h2] at hb
        obtain rfl := Option.some.inj hb
        exact Or.inr (Or.inl ha)
      · refine Or.inr (Or.inr ⟨t, ?_, pc, hb, hc, ha⟩)
        intro hmem
        simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hmem
        have key : ∀ {d : Nat}, t.val = d → t = toSq d :=
          fun hd => (toSq_val t).symm.trans (congrArg toSq hd)
        rcases hmem with h | h
        · rcases h with h | h
          · exact ht1 (key h)
          · exact ht2 (key h)
        · rcases h with h | h
          · exact ht1 (key h)
          · exact ht2 (key h)
  · rintro (ha | ha | ⟨t, -, pc, hb, hc, ha⟩)
    · exact ⟨toSq d₁, pc₁, h1, hc1, ha⟩
    · exact ⟨toSq d₂, pc₂, h2, hc2, ha⟩
    · exact ⟨t, pc, hb, hc, ha⟩

theorem castleRhs_pseudo_K (hf : Fits c p) (hkwe : c.kw = E1)
    (hsafe4 : attacked p.board (toSq E1) .black = false) :
    ((⟨toSq E1, toSq G1, none⟩ : Move) ∈ pseudo p) ↔
      (p.castleK .white = true ∧ p.board (toSq F1) = none ∧ p.board (toSq G1) = none ∧
        attacked p.board (toSq F1) .black = false) := by
  obtain ⟨hpwb, hpbb, hsym⟩ := fits_kings hf
  have hturn : p.turn = .white := hf.2.1
  have hpb4 : p.board (toSq E1) = some ⟨.white, .king⟩ := hkwe ▸ hpwb
  constructor
  · intro hps
    rcases pseudo_cases hps with ⟨s', q', hbs, hcol, hpm⟩ | hcm
    · exact (castleK_mv_not_piece p hpb4 hbs hpm).elim
    · obtain ⟨hb1, hs4, hck, hr7, h5, h6, hs5⟩ := (castleMoves_iff_K p hturn).mp hcm
      exact ⟨hck, h5, h6, hs5⟩
  · rintro ⟨hck, h5, h6, hs5⟩
    exact mem_pseudo_of_castle ((castleMoves_iff_K p hturn).mpr
      ⟨hpb4, hsafe4, hck, tsq7.symm ▸ (hf.1.castleK .white hck).2, h5, h6, hs5⟩)

theorem castleRhs_pseudo_Q (hf : Fits c p) (hkwe : c.kw = E1)
    (hsafe4 : attacked p.board (toSq E1) .black = false) :
    ((⟨toSq E1, toSq C1, none⟩ : Move) ∈ pseudo p) ↔
      (p.castleQ .white = true ∧ p.board (toSq B1) = none ∧ p.board (toSq C1) = none ∧
        p.board (toSq D1) = none ∧ attacked p.board (toSq D1) .black = false) := by
  obtain ⟨hpwb, hpbb, hsym⟩ := fits_kings hf
  have hturn : p.turn = .white := hf.2.1
  have hpb4 : p.board (toSq E1) = some ⟨.white, .king⟩ := hkwe ▸ hpwb
  constructor
  · intro hps
    rcases pseudo_cases hps with ⟨s', q', hbs, hcol, hpm⟩ | hcm
    · exact (castleQ_mv_not_piece p hpb4 hbs hpm).elim
    · obtain ⟨hb1, hs4, hck, hr0, h1, h2, h3, hs3⟩ := (castleMoves_iff_Q p hturn).mp hcm
      exact ⟨hck, h1, h2, h3, hs3⟩
  · rintro ⟨hck, h1, h2, h3, hs3⟩
    exact mem_pseudo_of_castle ((castleMoves_iff_Q p hturn).mpr
      ⟨hpb4, hsafe4, hck, tsq0.symm ▸ (hf.1.castleQ .white hck).2, h1, h2, h3, hs3⟩)

theorem castle_legal (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hr : RightsOk c s r)
    (m : Cand) (hm : m ∈ c.castleCands r) : m.legal.eval A = decide (m.mv ∈ legalMoves p) := by
  rcases castleCands_unpack hm with ⟨v, hlk, hmEq⟩ | ⟨v, hlk, hmEq⟩
  · subst hmEq
    have his : (r.cr.lookup true).isSome = true := by rw [hlk]; rfl
    have hcfg : (c.kw == E1 && !c.chk && (if true then H1 else A1) != c.kb) = true :=
      (hr.2.2.2 true) ▸ his
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcfg
    obtain ⟨⟨hkwe, hchk'⟩, hcor⟩ := hcfg
    have hcor' : H1 ≠ c.kb := hcor
    have hchkf : c.chk = false := Bool.not_eq_true' _ ▸ hchk'
    have hchkI : inCheck p .white = false := by
      have e : inCheck p .white = c.chk := congrArg Cfg.chk hf.2.2
      exact e.trans hchkf
    have hsafe4 : attacked p.board (toSq E1) .black = false := by
      have hk2 : kingSq p .white = toSq E1 :=
        Fin.ext ((congrArg Cfg.kw hf.2.2).trans (hkwe.trans (toSq_val_of_lt E1 (by decide)).symm))
      have h1 := inCheck_iff_attacked p .white (hf.1.kings .white)
      rw [hk2] at h1
      exact h1.symm.trans hchkI
    obtain ⟨hpbC, hlocWK, hswG⟩ := castleK_play_facts hf hkwe
    have hpsI := castleRhs_pseudo_K hf hkwe hsafe4
    have hturn : p.turn = .white := hf.2.1
    have hva : (Ex.v v).eval A = p.castleK .white := eval_v_cr hg hr true v hlk
    have he5 : (c.empty F1).eval A = (p.board (toSq F1)).isNone :=
      eval_empty hf hg hl F1 (by decide)
    have he6 : (c.empty G1).eval A = (p.board (toSq G1)).isNone :=
      eval_empty hf hg hl G1 (by decide)
    have ha4 : (c.attB E1 [E1] [] []).eval A = attacked p.board (toSq E1) .black :=
      (eval_attB_vac hf hg hl E1 E1 (by decide) hkwe.symm).trans
        (attacked_congr_off (fun t ht2 => by rw [if_neg ht2]))
    have ha5 : (c.attB F1 [E1] [] []).eval A = attacked p.board (toSq F1) .black := by
      refine (eval_attB_vac hf hg hl E1 F1 (by decide) hkwe.symm).trans ?_
      exact attacked_vac (fun pc hpc => by
        rw [show p.board (toSq E1) = some ⟨.white, .king⟩ from hkwe ▸ (fits_kings hf).1] at hpc
        obtain rfl := Option.some.inj hpc
        decide) hsafe4
    show (Ex.and [.v v, c.empty F1, c.empty G1, Ex.not (c.attB E1 [E1] [] []),
        Ex.not (c.attB F1 [E1] [] []), Ex.not (c.attB G1 [E1, H1] [F1] [])]).eval A =
      decide (⟨toSq E1, toSq G1, none⟩ ∈ legalMoves p)
    cases hck : p.castleK .white with
    | false =>
      rw [eval_and6, hva, hck, Bool.false_and]
      rw [show (decide ((⟨toSq E1, toSq G1, none⟩ : Move) ∈ legalMoves p)) = false from
        decide_eq_false_iff_not.mpr (fun hmem => by
          have hx := (hpsI.mp (mem_legalMoves hmem).1).1
          rw [hck] at hx
          exact absurd hx (by decide))]
    | true =>
      have hrook7 : p.board (toSq H1) = some ⟨.white, .rook⟩ :=
        tsq7.symm ▸ (hf.1.castleK .white hck).2
      obtain ⟨hkw64, hkb64, hcheb12⟩ := fits_cfgOk hf
      have hkbnkw : c.kb ≠ c.kw := by
        intro e
        rw [e, cheb_self] at hcheb12
        omega
      have hkbnE1 : c.kb ≠ E1 := fun e => hkbnkw (e.trans hkwe.symm)
      have hkbnF1 : c.kb ≠ F1 := by
        intro e
        have h2 : cheb c.kw c.kb = cheb E1 F1 := by rw [hkwe, e]
        rw [h2] at hcheb12
        have h3 : cheb E1 F1 = 1 := by decide
        omega
      have ha6 : (c.attB G1 [E1, H1] [F1] []).eval A =
          attacked (play p ⟨toSq E1, toSq G1, none⟩).board (toSq G1) .black := by
        refine eval_attB_play hf hg hl G1 E1 H1 F1 ⟨toSq E1, toSq G1, none⟩
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by rw [hpbC (toSq E1), if_neg (by decide), if_pos rfl])
          (by rw [hpbC (toSq H1), if_neg (by decide), if_neg (by decide), if_neg (by decide),
            if_pos rfl])
          (by
            rw [hpbC (toSq F1), if_neg (by decide), if_neg (by decide), if_pos rfl]
            exact hrook7)
          (by
            intro q hq hE hH hF hG
            rw [hpbC (toSq q), if_neg (fun e => hG (toSq_inj_of_lt hq (by decide) e)),
              if_neg (fun e => hE (toSq_inj_of_lt hq (by decide) e)),
              if_neg (fun e => hF (toSq_inj_of_lt hq (by decide) e)),
              if_neg (fun e => hH (toSq_inj_of_lt hq (by decide) e))])
          hkbnE1 (fun e => hcor' e.symm) hkbnF1 (by rw [hkwe]; decide)
      have ha4' : (Ex.not (c.attB E1 [E1] [] [])).eval A = !attacked p.board (toSq E1) .black :=
        congrArg Bool.not ha4
      have ha5' : (Ex.not (c.attB F1 [E1] [] [])).eval A = !attacked p.board (toSq F1) .black :=
        congrArg Bool.not ha5
      have ha6' : (Ex.not (c.attB G1 [E1, H1] [F1] [])).eval A =
          !attacked (play p ⟨toSq E1, toSq G1, none⟩).board (toSq G1) .black :=
        congrArg Bool.not ha6
      have hLeg : ((⟨toSq E1, toSq G1, none⟩ : Move) ∈ legalMoves p) ↔
          ((⟨toSq E1, toSq G1, none⟩ : Move) ∈ pseudo p ∧
            inCheck (play p ⟨toSq E1, toSq G1, none⟩) p.turn = false) := by
        unfold legalMoves
        rw [List.mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, Bool.not_eq_true' _ ▸ h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, (Bool.not_eq_true' _).symm ▸ h2⟩
      have hInc : inCheck (play p ⟨toSq E1, toSq G1, none⟩) p.turn =
          attacked (play p ⟨toSq E1, toSq G1, none⟩).board (toSq G1) .black := by
        rw [hturn]
        unfold inCheck
        exact inCheck_eq_of_uniq hswG (fun s2 hs => (hlocWK s2).mp hs)
      rw [eval_and6, hva, he5, he6, ha4', ha5', ha6']
      rw [hsafe4, Bool.not_false, hck, Bool.true_and, Bool.true_and]
      rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Bool.not_eq_true', Bool.not_eq_true', decide_eq_true_iff]
      rw [hLeg, hInc]
      constructor
      · rintro ⟨h5, h6, hs5, hs6⟩
        exact ⟨hpsI.mpr ⟨hck, Option.isNone_iff_eq_none.mp h5,
          Option.isNone_iff_eq_none.mp h6, hs5⟩, hs6⟩
      · rintro ⟨hps, hs6⟩
        have hkf := hpsI.mp hps
        exact ⟨Option.isNone_iff_eq_none.mpr hkf.2.1, Option.isNone_iff_eq_none.mpr hkf.2.2.1,
          hkf.2.2.2, hs6⟩
  · subst hmEq
    have his : (r.cr.lookup false).isSome = true := by rw [hlk]; rfl
    have hcfg : (c.kw == E1 && !c.chk && (if false then H1 else A1) != c.kb) = true :=
      (hr.2.2.2 false) ▸ his
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcfg
    obtain ⟨⟨hkwe, hchk'⟩, hcor⟩ := hcfg
    have hcor' : A1 ≠ c.kb := hcor
    have hchkf : c.chk = false := Bool.not_eq_true' _ ▸ hchk'
    have hchkI : inCheck p .white = false := by
      have e : inCheck p .white = c.chk := congrArg Cfg.chk hf.2.2
      exact e.trans hchkf
    have hsafe4 : attacked p.board (toSq E1) .black = false := by
      have hk2 : kingSq p .white = toSq E1 :=
        Fin.ext ((congrArg Cfg.kw hf.2.2).trans (hkwe.trans (toSq_val_of_lt E1 (by decide)).symm))
      have h1 := inCheck_iff_attacked p .white (hf.1.kings .white)
      rw [hk2] at h1
      exact h1.symm.trans hchkI
    obtain ⟨hpbC, hlocWC, hswC⟩ := castleQ_play_facts hf hkwe
    have hpsI := castleRhs_pseudo_Q hf hkwe hsafe4
    have hturn : p.turn = .white := hf.2.1
    have hva : (Ex.v v).eval A = p.castleQ .white := eval_v_cr hg hr false v hlk
    have he1 : (c.empty B1).eval A = (p.board (toSq B1)).isNone :=
      eval_empty hf hg hl B1 (by decide)
    have he2 : (c.empty C1).eval A = (p.board (toSq C1)).isNone :=
      eval_empty hf hg hl C1 (by decide)
    have he3 : (c.empty D1).eval A = (p.board (toSq D1)).isNone :=
      eval_empty hf hg hl D1 (by decide)
    have ha4 : (c.attB E1 [E1] [] []).eval A = attacked p.board (toSq E1) .black :=
      (eval_attB_vac hf hg hl E1 E1 (by decide) hkwe.symm).trans
        (attacked_congr_off (fun t ht2 => by rw [if_neg ht2]))
    have ha5 : (c.attB D1 [E1] [] []).eval A = attacked p.board (toSq D1) .black := by
      refine (eval_attB_vac hf hg hl E1 D1 (by decide) hkwe.symm).trans ?_
      exact attacked_vac (fun pc hpc => by
        rw [show p.board (toSq E1) = some ⟨.white, .king⟩ from hkwe ▸ (fits_kings hf).1] at hpc
        obtain rfl := Option.some.inj hpc
        decide) hsafe4
    show (Ex.and [.v v, c.empty B1, c.empty C1, c.empty D1, Ex.not (c.attB E1 [E1] [] []),
        Ex.not (c.attB D1 [E1] [] []), Ex.not (c.attB C1 [E1, A1] [D1] [])]).eval A =
      decide (⟨toSq E1, toSq C1, none⟩ ∈ legalMoves p)
    cases hck : p.castleQ .white with
    | false =>
      rw [eval_and7, hva, hck, Bool.false_and]
      rw [show (decide ((⟨toSq E1, toSq C1, none⟩ : Move) ∈ legalMoves p)) = false from
        decide_eq_false_iff_not.mpr (fun hmem => by
          have hx := (hpsI.mp (mem_legalMoves hmem).1).1
          rw [hck] at hx
          exact absurd hx (by decide))]
    | true =>
      have hrook0 : p.board (toSq A1) = some ⟨.white, .rook⟩ :=
        tsq0.symm ▸ (hf.1.castleQ .white hck).2
      obtain ⟨hkw64, hkb64, hcheb12⟩ := fits_cfgOk hf
      have hkbnkw : c.kb ≠ c.kw := by
        intro e
        rw [e, cheb_self] at hcheb12
        omega
      have hkbnE1 : c.kb ≠ E1 := fun e => hkbnkw (e.trans hkwe.symm)
      have hkbnD1 : c.kb ≠ D1 := by
        intro e
        have h2 : cheb c.kw c.kb = cheb E1 D1 := by rw [hkwe, e]
        rw [h2] at hcheb12
        have h3 : cheb E1 D1 = 1 := by decide
        omega
      have ha6 : (c.attB C1 [E1, A1] [D1] []).eval A =
          attacked (play p ⟨toSq E1, toSq C1, none⟩).board (toSq C1) .black := by
        refine eval_attB_play hf hg hl C1 E1 A1 D1 ⟨toSq E1, toSq C1, none⟩
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by rw [hpbC (toSq E1), if_neg (by decide), if_pos rfl])
          (by rw [hpbC (toSq A1), if_neg (by decide), if_neg (by decide), if_neg (by decide),
            if_pos rfl])
          (by
            rw [hpbC (toSq D1), if_neg (by decide), if_neg (by decide), if_pos rfl]
            exact hrook0)
          (by
            intro q hq hE hH hF hG
            rw [hpbC (toSq q), if_neg (fun e => hG (toSq_inj_of_lt hq (by decide) e)),
              if_neg (fun e => hE (toSq_inj_of_lt hq (by decide) e)),
              if_neg (fun e => hF (toSq_inj_of_lt hq (by decide) e)),
              if_neg (fun e => hH (toSq_inj_of_lt hq (by decide) e))])
          hkbnE1 (fun e => hcor' e.symm) hkbnD1 (by rw [hkwe]; decide)
      have ha4' : (Ex.not (c.attB E1 [E1] [] [])).eval A = !attacked p.board (toSq E1) .black :=
        congrArg Bool.not ha4
      have ha5' : (Ex.not (c.attB D1 [E1] [] [])).eval A = !attacked p.board (toSq D1) .black :=
        congrArg Bool.not ha5
      have ha6' : (Ex.not (c.attB C1 [E1, A1] [D1] [])).eval A =
          !attacked (play p ⟨toSq E1, toSq C1, none⟩).board (toSq C1) .black :=
        congrArg Bool.not ha6
      have hLeg : ((⟨toSq E1, toSq C1, none⟩ : Move) ∈ legalMoves p) ↔
          ((⟨toSq E1, toSq C1, none⟩ : Move) ∈ pseudo p ∧
            inCheck (play p ⟨toSq E1, toSq C1, none⟩) p.turn = false) := by
        unfold legalMoves
        rw [List.mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, Bool.not_eq_true' _ ▸ h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, (Bool.not_eq_true' _).symm ▸ h2⟩
      have hInc : inCheck (play p ⟨toSq E1, toSq C1, none⟩) p.turn =
          attacked (play p ⟨toSq E1, toSq C1, none⟩).board (toSq C1) .black := by
        rw [hturn]
        unfold inCheck
        exact inCheck_eq_of_uniq hswC (fun s2 hs => (hlocWC s2).mp hs)
      rw [eval_and7, hva, he1, he2, he3, ha4', ha5', ha6']
      rw [hsafe4, Bool.not_false, hck, Bool.true_and, Bool.true_and]
      rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', decide_eq_true_iff]
      rw [hLeg, hInc]
      constructor
      · rintro ⟨h1, h2, h3, hs3, hs6⟩
        exact ⟨hpsI.mpr ⟨hck, Option.isNone_iff_eq_none.mp h1, Option.isNone_iff_eq_none.mp h2,
          Option.isNone_iff_eq_none.mp h3, hs3⟩, hs6⟩
      · rintro ⟨hps, hs6⟩
        have hkf := hpsI.mp hps
        exact ⟨Option.isNone_iff_eq_none.mpr hkf.2.1, Option.isNone_iff_eq_none.mpr hkf.2.2.1,
          Option.isNone_iff_eq_none.mpr hkf.2.2.2.1, hkf.2.2.2.2, hs6⟩

theorem castle_chk (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hr : RightsOk c s r)
    (m : Cand) (hm : m ∈ c.castleCands r) (h : m.mv ∈ legalMoves p) : m.chk.eval A = givesCheck p m.mv := by
  rcases castleCands_unpack hm with ⟨v, hlk, hmEq⟩ | ⟨v, hlk, hmEq⟩
  · subst hmEq
    have his : (r.cr.lookup true).isSome = true := by rw [hlk]; rfl
    have hcfg : (c.kw == E1 && !c.chk && (if true then H1 else A1) != c.kb) = true :=
      (hr.2.2.2 true) ▸ his
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcfg
    obtain ⟨⟨hkwe, hchk'⟩, hcor⟩ := hcfg
    have hcor' : H1 ≠ c.kb := hcor
    have hchkf : c.chk = false := Bool.not_eq_true' _ ▸ hchk'
    have hchkI : inCheck p .white = false := by
      have e : inCheck p .white = c.chk := congrArg Cfg.chk hf.2.2
      exact e.trans hchkf
    have hsafe4 : attacked p.board (toSq E1) .black = false := by
      have hk2 : kingSq p .white = toSq E1 :=
        Fin.ext ((congrArg Cfg.kw hf.2.2).trans (hkwe.trans (toSq_val_of_lt E1 (by decide)).symm))
      have h1 := inCheck_iff_attacked p .white (hf.1.kings .white)
      rw [hk2] at h1
      exact h1.symm.trans hchkI
    obtain ⟨hpbC, hlocWK, hswG⟩ := castleK_play_facts hf hkwe
    have hpsI := castleRhs_pseudo_K hf hkwe hsafe4
    have hturn : p.turn = .white := hf.2.1
    have hlegK : (⟨toSq E1, toSq G1, none⟩ : Move) ∈ legalMoves p := h
    obtain ⟨hpsm, hic⟩ := mem_legalMoves hlegK
    obtain ⟨hck', h5, h6, hs5⟩ := hpsI.mp hpsm
    have hrook7 : p.board (toSq H1) = some ⟨.white, .rook⟩ :=
      tsq7.symm ▸ (hf.1.castleK .white hck').2
    obtain ⟨hpwb, hpbb, -⟩ := fits_kings hf
    obtain ⟨hkw64, hkb64, hcheb12⟩ := fits_cfgOk hf
    have hkbnkw : c.kb ≠ c.kw := by
      intro e
      rw [e, cheb_self] at hcheb12
      omega
    have hkbnE1 : c.kb ≠ E1 := fun e => hkbnkw (e.trans hkwe.symm)
    have hkbnF1 : c.kb ≠ F1 := by
      intro e
      have h2 : cheb c.kw c.kb = cheb E1 F1 := by rw [hkwe, e]
      rw [h2] at hcheb12
      have h3 : cheb E1 F1 = 1 := by decide
      omega
    have hkbnG1 : c.kb ≠ G1 := by
      intro e
      have h2 := hpbb
      rw [e] at h2
      rw [h6] at h2
      simp at h2
    have hsbP : (play p ⟨toSq E1, toSq G1, none⟩).board (toSq c.kb) = some ⟨.black, .king⟩ := by
      rw [hpbC (toSq c.kb), if_neg (fun e => hkbnG1 (toSq_inj_of_lt hkb64 (by decide) e)),
        if_neg (fun e => hkbnE1 (toSq_inj_of_lt hkb64 (by decide) e)),
        if_neg (fun e => hkbnF1 (toSq_inj_of_lt hkb64 (by decide) e)),
        if_neg (fun e => hcor' (toSq_inj_of_lt hkb64 (by decide) e).symm)]
      exact hpbb
    have hkb2 : toSq c.kb = kingSq p .black :=
      Fin.ext (by rw [toSq_val_of_lt c.kb hkb64]; exact (congrArg Cfg.kb hf.2.2).symm)
    have hpbu' : ∀ s, p.board s = some ⟨.black, .king⟩ → s = toSq c.kb :=
      fun s2 hs => ((kingSq_spec p .black (hf.1.kings .black)).2 s2 hs).trans hkb2.symm
    have hlocBK : ∀ s2 : Sq, (play p ⟨toSq E1, toSq G1, none⟩).board s2 = some ⟨.black, .king⟩ ↔
        s2 = toSq c.kb := by
      intro s2
      rw [hpbC s2]
      by_cases h1 : s2 = toSq G1
      · rw [if_pos h1]
        constructor
        · intro hh
          have h2 := Option.some.inj hh
          simp only [Piece.mk.injEq] at h2
          exact absurd h2.1 (by decide)
        · intro hh
          exact absurd (toSq_inj_of_lt (by decide) hkb64 (h1 ▸ hh)).symm hkbnG1
      · rw [if_neg h1]
        by_cases h2 : s2 = toSq E1
        · rw [if_pos h2]
          exact ⟨fun hh => by simp at hh, fun hh =>
            absurd (toSq_inj_of_lt (by decide) hkb64 (h2 ▸ hh)) (fun e => hkbnE1 e.symm)⟩
        · rw [if_neg h2]
          by_cases h3 : s2 = toSq F1
          · rw [if_pos h3]
            constructor
            · intro hh
              rw [hrook7] at hh
              have e2 := Option.some.inj hh
              simp only [Piece.mk.injEq] at e2
              exact absurd e2.1 (by decide)
            · intro hh
              exact absurd ((toSq_inj_of_lt (by decide) hkb64 (h3 ▸ hh)).symm) hkbnF1
          · rw [if_neg h3]
            by_cases h4 : s2 = toSq H1
            · rw [if_pos h4]
              exact ⟨fun hh => by simp at hh, fun hh =>
                absurd (toSq_inj_of_lt (by decide) hkb64 (h4 ▸ hh)) hcor'⟩
            · rw [if_neg h4]
              exact ⟨hpbu' s2, fun hh => hh.symm ▸ hpbb⟩
    have hkxG : cheb G1 c.kb ≠ 1 := by
      intro h1
      have hAdmP : Admissible (play p ⟨toSq E1, toSq G1, none⟩) := admissible_play hf.1 hlegK
      obtain ⟨hwp1, hwu1⟩ := kingSq_spec (play p ⟨toSq E1, toSq G1, none⟩) .white
        (play_kings hf.1 hlegK .white)
      obtain ⟨hbp1', hbu1⟩ := kingSq_spec (play p ⟨toSq E1, toSq G1, none⟩) .black
        (play_kings hf.1 hlegK .black)
      have hkWsq : kingSq (play p ⟨toSq E1, toSq G1, none⟩) .white = toSq G1 :=
        (hwu1 (toSq G1) hswG).symm
      have hkBsq : kingSq (play p ⟨toSq E1, toSq G1, none⟩) .black = toSq c.kb :=
        (hbu1 (toSq c.kb) hsbP).symm
      have hap := hAdmP.apart
      rw [hkWsq, hkBsq] at hap
      rw [← cheb_toSq G1 c.kb (by decide) hkb64] at hap
      omega
    have hdir : (c.direct F1 3 [E1, H1] [G1]).eval A =
        (attacks (play p ⟨toSq E1, toSq G1, none⟩).board (toSq F1) ⟨.white, .rook⟩).contains
          (toSq c.kb) := by
      refine eval_direct hf hg hl F1 3 (by decide) (by decide) [E1, H1] [G1]
        (play p ⟨toSq E1, toSq G1, none⟩).board ?_ ?_ ?_ ?_
      · intro q hq hqG
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact absurd hqG (by decide)
        · exact absurd hqG (by decide)
      · intro q hq hqE hqG
        have hq64 := between_lt64 hq
        have hnot : q ≠ G1 ∧ q ≠ E1 ∧ q ≠ F1 ∧ q ≠ H1 := by
          refine ⟨fun e => hqG (List.mem_singleton.mpr e), ?_,
            (mem_between_ne (by decide) hkb64 hq).1, ?_⟩
          · intro e; exact hqE (List.mem_cons.mpr (Or.inl e))
          · intro e; exact hqE (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr e)))
        rw [hpbC (toSq q), if_neg (fun e => hnot.1 (toSq_inj_of_lt hq64 (by decide) e)),
          if_neg (fun e => hnot.2.1 (toSq_inj_of_lt hq64 (by decide) e)),
          if_neg (fun e => hnot.2.2.1 (toSq_inj_of_lt hq64 (by decide) e)),
          if_neg (fun e => hnot.2.2.2 (toSq_inj_of_lt hq64 (by decide) e))]
      · intro q hq hqEm hqG
        rw [List.mem_cons, List.mem_singleton] at hqEm
        rcases hqEm with hqEm | hqEm
        · subst hqEm
          rw [hpbC (toSq E1), if_neg (by decide), if_pos rfl]
        · subst hqEm
          rw [hpbC (toSq H1), if_neg (by decide), if_neg (by decide), if_neg (by decide),
            if_pos rfl]
      · intro q hq hqG
        rw [List.mem_singleton] at hqG
        subst hqG
        rw [hswG]
        exact Option.some_ne_none _
    have hattW : (c.attW c.kb [E1, H1] [F1, G1] [F1, G1] G1).eval A =
        decide (∃ t : Sq, t.val ∉ [F1, G1] ++ [F1, G1] ∧ ∃ pc,
          (play p ⟨toSq E1, toSq G1, none⟩).board t = some pc ∧ pc.color = colOf true ∧
          toSq c.kb ∈ attacks (play p ⟨toSq E1, toSq G1, none⟩).board t pc) := by
      refine eval_att hf hg hl c.kb hkb64 true G1 (by decide) [E1, H1] [F1, G1] [F1, G1]
        (play p ⟨toSq E1, toSq G1, none⟩).board ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · refine ⟨?_, ?_, ?_⟩
        · intro q hq hqE hqO _
          have hnot : q ≠ G1 ∧ q ≠ E1 ∧ q ≠ F1 ∧ q ≠ H1 := by
            refine ⟨fun e => hqO (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr e))), ?_, ?_, ?_⟩
            · intro e; exact hqE (List.mem_cons.mpr (Or.inl e))
            · intro e; exact hqO (List.mem_cons.mpr (Or.inl e))
            · intro e; exact hqE (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr e)))
          rw [hpbC (toSq q), if_neg (fun e => hnot.1 (toSq_inj_of_lt hq (by decide) e)),
            if_neg (fun e => hnot.2.1 (toSq_inj_of_lt hq (by decide) e)),
            if_neg (fun e => hnot.2.2.1 (toSq_inj_of_lt hq (by decide) e)),
            if_neg (fun e => hnot.2.2.2 (toSq_inj_of_lt hq (by decide) e))]
        · intro q hqE hqO
          rw [List.mem_cons, List.mem_singleton] at hqE
          rcases hqE with hqE | hqE
          · subst hqE
            rw [hpbC (toSq E1), if_neg (by decide), if_pos rfl]
          · subst hqE
            rw [hpbC (toSq H1), if_neg (by decide), if_neg (by decide), if_neg (by decide),
              if_pos rfl]
        · intro q hqO
          rw [List.mem_cons, List.mem_singleton] at hqO
          rcases hqO with hqO | hqO
          · subst hqO
            rw [hpbC (toSq F1), if_neg (by decide), if_neg (by decide), if_pos rfl]
            rw [hrook7]
            exact Option.some_ne_none _
          · subst hqO
            rw [hswG]
            exact Option.some_ne_none _
      · intro q hqO
        exact Or.inl hqO
      · intro q hqE hm2
        rw [List.mem_cons, List.mem_singleton] at hqE
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm2
        rcases hqE with rfl | rfl <;> rcases hm2 with hm2 | hm2 <;> exact absurd hm2 (by decide)
      · intro q hqE
        rw [List.mem_cons, List.mem_singleton] at hqE
        rcases hqE with rfl | rfl
        · decide
        · decide
      · intro q hqO
        rw [List.mem_cons, List.mem_singleton] at hqO
        rcases hqO with rfl | rfl
        · decide
        · decide
      · intro t
        show _ ↔ t = toSq G1
        exact hlocWK t
      · intro h1 _
        exact absurd h1 hkxG
      · intro hm
        simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hm
        rcases hm with (hm | hm) | (hm | hm)
        · exact hkbnE1 hm
        · exact (fun e => hcor' e.symm) hm
        · exact hkbnF1 hm
        · exact hkbnG1 hm
      · intro hm
        rw [hkwe] at hm
        exact absurd hm (by decide)
    have hgc : givesCheck p ⟨toSq E1, toSq G1, none⟩ =
        attacked (play p ⟨toSq E1, toSq G1, none⟩).board (toSq c.kb) .white := by
      show inCheck (play p ⟨toSq E1, toSq G1, none⟩) p.turn.opp = _
      rw [hturn]
      unfold inCheck
      exact inCheck_eq_of_uniq hsbP (fun s2 hs => (hlocBK s2).mp hs)
    have ho3' : (play p ⟨toSq E1, toSq G1, none⟩).board (toSq F1) = some ⟨.white, .rook⟩ := by
      rw [hpbC (toSq F1), if_neg (by decide), if_neg (by decide), if_pos rfl]
      exact hrook7
    have hdirMem : (attacks (play p ⟨toSq E1, toSq G1, none⟩).board (toSq F1) ⟨.white, .rook⟩).contains
        (toSq c.kb) = decide (toSq c.kb ∈ attacks (play p ⟨toSq E1, toSq G1, none⟩).board (toSq F1)
          ⟨.white, .rook⟩) := by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_iff]
    have hGf : ¬ (toSq c.kb ∈ attacks (play p ⟨toSq E1, toSq G1, none⟩).board (toSq G1)
        ⟨.white, .king⟩) := by
      intro hh
      have h1 := (mem_attacks_king _ (toSq G1) (toSq c.kb) .white).mp hh
      rw [toSq_val_of_lt G1 (by decide), toSq_val_of_lt c.kb hkb64] at h1
      exact hkxG h1
    have hsplit := attSplit2 (b' := (play p ⟨toSq E1, toSq G1, none⟩).board) (s := toSq c.kb)
      (d₁ := F1) (d₂ := G1) (col := .white) (pc₁ := ⟨.white, .rook⟩) (pc₂ := ⟨.white, .king⟩)
      ho3' rfl hswG rfl
    show (Ex.or [c.direct F1 3 [E1, H1] [G1], c.attW c.kb [E1, H1] [F1, G1] [F1, G1] G1]).eval A =
      givesCheck p ⟨toSq E1, toSq G1, none⟩
    rw [eval_or2, hdir, hattW, hgc]
    rw [hdirMem, Bool.eq_iff_iff, Bool.or_eq_true, attacked_iff, decide_eq_true_iff,
      decide_eq_true_iff]
    constructor
    · rintro (h1o | h2o)
      · exact hsplit.mpr (Or.inl h1o)
      · exact hsplit.mpr (Or.inr (Or.inr h2o))
    · intro hQ
      rcases hsplit.mp hQ with h1o | h2o | h3o
      · exact Or.inl h1o
      · exact absurd h2o hGf
      · exact Or.inr h3o
  · subst hmEq
    have his : (r.cr.lookup false).isSome = true := by rw [hlk]; rfl
    have hcfg : (c.kw == E1 && !c.chk && (if false then H1 else A1) != c.kb) = true :=
      (hr.2.2.2 false) ▸ his
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcfg
    obtain ⟨⟨hkwe, hchk'⟩, hcor⟩ := hcfg
    have hcor' : A1 ≠ c.kb := hcor
    have hchkf : c.chk = false := Bool.not_eq_true' _ ▸ hchk'
    have hchkI : inCheck p .white = false := by
      have e : inCheck p .white = c.chk := congrArg Cfg.chk hf.2.2
      exact e.trans hchkf
    have hsafe4 : attacked p.board (toSq E1) .black = false := by
      have hk2 : kingSq p .white = toSq E1 :=
        Fin.ext ((congrArg Cfg.kw hf.2.2).trans (hkwe.trans (toSq_val_of_lt E1 (by decide)).symm))
      have h1 := inCheck_iff_attacked p .white (hf.1.kings .white)
      rw [hk2] at h1
      exact h1.symm.trans hchkI
    obtain ⟨hpbC, hlocWC, hswC⟩ := castleQ_play_facts hf hkwe
    have hpsI := castleRhs_pseudo_Q hf hkwe hsafe4
    have hturn : p.turn = .white := hf.2.1
    have hlegQ : (⟨toSq E1, toSq C1, none⟩ : Move) ∈ legalMoves p := h
    obtain ⟨hpsm, hic⟩ := mem_legalMoves hlegQ
    obtain ⟨hck', h1, h2, h3, hs3⟩ := hpsI.mp hpsm
    have hrook0 : p.board (toSq A1) = some ⟨.white, .rook⟩ :=
      tsq0.symm ▸ (hf.1.castleQ .white hck').2
    obtain ⟨hpwb, hpbb, -⟩ := fits_kings hf
    obtain ⟨hkw64, hkb64, hcheb12⟩ := fits_cfgOk hf
    have hkbnkw : c.kb ≠ c.kw := by
      intro e
      rw [e, cheb_self] at hcheb12
      omega
    have hkbnE1 : c.kb ≠ E1 := fun e => hkbnkw (e.trans hkwe.symm)
    have hkbnD1 : c.kb ≠ D1 := by
      intro e
      have h2 : cheb c.kw c.kb = cheb E1 D1 := by rw [hkwe, e]
      rw [h2] at hcheb12
      have h3 : cheb E1 D1 = 1 := by decide
      omega
    have hkbnC1 : c.kb ≠ C1 := by
      intro e
      have h4 := hpbb
      rw [e] at h4
      rw [h2] at h4
      simp at h4
    have hsbP : (play p ⟨toSq E1, toSq C1, none⟩).board (toSq c.kb) = some ⟨.black, .king⟩ := by
      rw [hpbC (toSq c.kb), if_neg (fun e => hkbnC1 (toSq_inj_of_lt hkb64 (by decide) e)),
        if_neg (fun e => hkbnE1 (toSq_inj_of_lt hkb64 (by decide) e)),
        if_neg (fun e => hkbnD1 (toSq_inj_of_lt hkb64 (by decide) e)),
        if_neg (fun e => hcor' (toSq_inj_of_lt hkb64 (by decide) e).symm)]
      exact hpbb
    have hkb2 : toSq c.kb = kingSq p .black :=
      Fin.ext (by rw [toSq_val_of_lt c.kb hkb64]; exact (congrArg Cfg.kb hf.2.2).symm)
    have hpbu' : ∀ s, p.board s = some ⟨.black, .king⟩ → s = toSq c.kb :=
      fun s2 hs => ((kingSq_spec p .black (hf.1.kings .black)).2 s2 hs).trans hkb2.symm
    have hlocBC : ∀ s2 : Sq, (play p ⟨toSq E1, toSq C1, none⟩).board s2 = some ⟨.black, .king⟩ ↔
        s2 = toSq c.kb := by
      intro s2
      rw [hpbC s2]
      by_cases h1 : s2 = toSq C1
      · rw [if_pos h1]
        constructor
        · intro hh
          have h2x := Option.some.inj hh
          simp only [Piece.mk.injEq] at h2x
          exact absurd h2x.1 (by decide)
        · intro hh
          exact absurd (toSq_inj_of_lt (by decide) hkb64 (h1 ▸ hh)).symm hkbnC1
      · rw [if_neg h1]
        by_cases h2 : s2 = toSq E1
        · rw [if_pos h2]
          exact ⟨fun hh => by simp at hh, fun hh =>
            absurd (toSq_inj_of_lt (by decide) hkb64 (h2 ▸ hh)) (fun e => hkbnE1 e.symm)⟩
        · rw [if_neg h2]
          by_cases h3 : s2 = toSq D1
          · rw [if_pos h3]
            constructor
            · intro hh
              rw [hrook0] at hh
              have e2 := Option.some.inj hh
              simp only [Piece.mk.injEq] at e2
              exact absurd e2.1 (by decide)
            · intro hh
              exact absurd ((toSq_inj_of_lt (by decide) hkb64 (h3 ▸ hh)).symm) hkbnD1
          · rw [if_neg h3]
            by_cases h4 : s2 = toSq A1
            · rw [if_pos h4]
              exact ⟨fun hh => by simp at hh, fun hh =>
                absurd (toSq_inj_of_lt (by decide) hkb64 (h4 ▸ hh)) hcor'⟩
            · rw [if_neg h4]
              exact ⟨hpbu' s2, fun hh => hh.symm ▸ hpbb⟩
    have hkxG : cheb C1 c.kb ≠ 1 := by
      intro h1
      have hAdmP : Admissible (play p ⟨toSq E1, toSq C1, none⟩) := admissible_play hf.1 hlegQ
      obtain ⟨hwp1, hwu1⟩ := kingSq_spec (play p ⟨toSq E1, toSq C1, none⟩) .white
        (play_kings hf.1 hlegQ .white)
      obtain ⟨hbp1', hbu1⟩ := kingSq_spec (play p ⟨toSq E1, toSq C1, none⟩) .black
        (play_kings hf.1 hlegQ .black)
      have hkWsq : kingSq (play p ⟨toSq E1, toSq C1, none⟩) .white = toSq C1 :=
        (hwu1 (toSq C1) hswC).symm
      have hkBsq : kingSq (play p ⟨toSq E1, toSq C1, none⟩) .black = toSq c.kb :=
        (hbu1 (toSq c.kb) hsbP).symm
      have hap := hAdmP.apart
      rw [hkWsq, hkBsq] at hap
      rw [← cheb_toSq C1 c.kb (by decide) hkb64] at hap
      omega
    have hdir : (c.direct D1 3 [E1, A1] [C1]).eval A =
        (attacks (play p ⟨toSq E1, toSq C1, none⟩).board (toSq D1) ⟨.white, .rook⟩).contains
          (toSq c.kb) := by
      refine eval_direct hf hg hl D1 3 (by decide) (by decide) [E1, A1] [C1]
        (play p ⟨toSq E1, toSq C1, none⟩).board ?_ ?_ ?_ ?_
      · intro q hq hqG
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact absurd hqG (by decide)
        · exact absurd hqG (by decide)
      · intro q hq hqE hqG
        have hq64 := between_lt64 hq
        have hnot : q ≠ C1 ∧ q ≠ E1 ∧ q ≠ D1 ∧ q ≠ A1 := by
          refine ⟨fun e => hqG (List.mem_singleton.mpr e), ?_,
            (mem_between_ne (by decide) hkb64 hq).1, ?_⟩
          · intro e; exact hqE (List.mem_cons.mpr (Or.inl e))
          · intro e; exact hqE (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr e)))
        rw [hpbC (toSq q), if_neg (fun e => hnot.1 (toSq_inj_of_lt hq64 (by decide) e)),
          if_neg (fun e => hnot.2.1 (toSq_inj_of_lt hq64 (by decide) e)),
          if_neg (fun e => hnot.2.2.1 (toSq_inj_of_lt hq64 (by decide) e)),
          if_neg (fun e => hnot.2.2.2 (toSq_inj_of_lt hq64 (by decide) e))]
      · intro q hq hqEm hqG
        rw [List.mem_cons, List.mem_singleton] at hqEm
        rcases hqEm with hqEm | hqEm
        · subst hqEm
          rw [hpbC (toSq E1), if_neg (by decide), if_pos rfl]
        · subst hqEm
          rw [hpbC (toSq A1), if_neg (by decide), if_neg (by decide), if_neg (by decide),
            if_pos rfl]
      · intro q hq hqG
        rw [List.mem_singleton] at hqG
        subst hqG
        rw [hswC]
        exact Option.some_ne_none _
    have hattW : (c.attW c.kb [E1, A1] [D1, C1] [D1, C1] C1).eval A =
        decide (∃ t : Sq, t.val ∉ [D1, C1] ++ [D1, C1] ∧ ∃ pc,
          (play p ⟨toSq E1, toSq C1, none⟩).board t = some pc ∧ pc.color = colOf true ∧
          toSq c.kb ∈ attacks (play p ⟨toSq E1, toSq C1, none⟩).board t pc) := by
      refine eval_att hf hg hl c.kb hkb64 true C1 (by decide) [E1, A1] [D1, C1] [D1, C1]
        (play p ⟨toSq E1, toSq C1, none⟩).board ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · refine ⟨?_, ?_, ?_⟩
        · intro q hq hqE hqO _
          have hnot : q ≠ C1 ∧ q ≠ E1 ∧ q ≠ D1 ∧ q ≠ A1 := by
            refine ⟨fun e => hqO (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr e))), ?_, ?_, ?_⟩
            · intro e; exact hqE (List.mem_cons.mpr (Or.inl e))
            · intro e; exact hqO (List.mem_cons.mpr (Or.inl e))
            · intro e; exact hqE (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr e)))
          rw [hpbC (toSq q), if_neg (fun e => hnot.1 (toSq_inj_of_lt hq (by decide) e)),
            if_neg (fun e => hnot.2.1 (toSq_inj_of_lt hq (by decide) e)),
            if_neg (fun e => hnot.2.2.1 (toSq_inj_of_lt hq (by decide) e)),
            if_neg (fun e => hnot.2.2.2 (toSq_inj_of_lt hq (by decide) e))]
        · intro q hqE hqO
          rw [List.mem_cons, List.mem_singleton] at hqE
          rcases hqE with hqE | hqE
          · subst hqE
            rw [hpbC (toSq E1), if_neg (by decide), if_pos rfl]
          · subst hqE
            rw [hpbC (toSq A1), if_neg (by decide), if_neg (by decide), if_neg (by decide),
              if_pos rfl]
        · intro q hqO
          rw [List.mem_cons, List.mem_singleton] at hqO
          rcases hqO with hqO | hqO
          · subst hqO
            rw [hpbC (toSq D1), if_neg (by decide), if_neg (by decide), if_pos rfl]
            rw [hrook0]
            exact Option.some_ne_none _
          · subst hqO
            rw [hswC]
            exact Option.some_ne_none _
      · intro q hqO
        exact Or.inl hqO
      · intro q hqE hm2
        rw [List.mem_cons, List.mem_singleton] at hqE
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm2
        rcases hqE with rfl | rfl <;> rcases hm2 with hm2 | hm2 <;> exact absurd hm2 (by decide)
      · intro q hqE
        rw [List.mem_cons, List.mem_singleton] at hqE
        rcases hqE with rfl | rfl
        · decide
        · decide
      · intro q hqO
        rw [List.mem_cons, List.mem_singleton] at hqO
        rcases hqO with rfl | rfl
        · decide
        · decide
      · intro t
        show _ ↔ t = toSq C1
        exact hlocWC t
      · intro h1 _
        exact absurd h1 hkxG
      · intro hm
        simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hm
        rcases hm with (hm | hm) | (hm | hm)
        · exact hkbnE1 hm
        · exact (fun e => hcor' e.symm) hm
        · exact hkbnD1 hm
        · exact hkbnC1 hm
      · intro hm
        rw [hkwe] at hm
        exact absurd hm (by decide)
    have hgc : givesCheck p ⟨toSq E1, toSq C1, none⟩ =
        attacked (play p ⟨toSq E1, toSq C1, none⟩).board (toSq c.kb) .white := by
      show inCheck (play p ⟨toSq E1, toSq C1, none⟩) p.turn.opp = _
      rw [hturn]
      unfold inCheck
      exact inCheck_eq_of_uniq hsbP (fun s2 hs => (hlocBC s2).mp hs)
    have ho3' : (play p ⟨toSq E1, toSq C1, none⟩).board (toSq D1) = some ⟨.white, .rook⟩ := by
      rw [hpbC (toSq D1), if_neg (by decide), if_neg (by decide), if_pos rfl]
      exact hrook0
    have hdirMem : (attacks (play p ⟨toSq E1, toSq C1, none⟩).board (toSq D1) ⟨.white, .rook⟩).contains
        (toSq c.kb) = decide (toSq c.kb ∈ attacks (play p ⟨toSq E1, toSq C1, none⟩).board (toSq D1)
          ⟨.white, .rook⟩) := by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_iff]
    have hGf : ¬ (toSq c.kb ∈ attacks (play p ⟨toSq E1, toSq C1, none⟩).board (toSq C1)
        ⟨.white, .king⟩) := by
      intro hh
      have h1 := (mem_attacks_king _ (toSq C1) (toSq c.kb) .white).mp hh
      rw [toSq_val_of_lt C1 (by decide), toSq_val_of_lt c.kb hkb64] at h1
      exact hkxG h1
    have hsplit := attSplit2 (b' := (play p ⟨toSq E1, toSq C1, none⟩).board) (s := toSq c.kb)
      (d₁ := D1) (d₂ := C1) (col := .white) (pc₁ := ⟨.white, .rook⟩) (pc₂ := ⟨.white, .king⟩)
      ho3' rfl hswC rfl
    show (Ex.or [c.direct D1 3 [E1, A1] [C1], c.attW c.kb [E1, A1] [D1, C1] [D1, C1] C1]).eval A =
      givesCheck p ⟨toSq E1, toSq C1, none⟩
    rw [eval_or2, hdir, hattW, hgc]
    rw [hdirMem, Bool.eq_iff_iff, Bool.or_eq_true, attacked_iff, decide_eq_true_iff,
      decide_eq_true_iff]
    constructor
    · rintro (h1o | h2o)
      · exact hsplit.mpr (Or.inl h1o)
      · exact hsplit.mpr (Or.inr (Or.inr h2o))
    · intro hQ
      rcases hsplit.mp hQ with h1o | h2o | h3o
      · exact Or.inl h1o
      · exact absurd h2o hGf
      · exact Or.inr h3o


theorem cand_legal (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hr : RightsOk c s r)
    (m : Cand) (hm : m ∈ c.cands r) (h : m.legal.eval A = true) : m.mv ∈ legalMoves p := by
  rcases (mem_cands m).mp hm with ⟨q, hq, hm⟩ | hm | hm
  · have hqb : q < 64 := List.mem_range.mp (List.mem_filter.mp hq).1
    have hK : c.isK q = false := by
      by_cases hKt : c.isK q = true
      · have h2 := (List.mem_filter.mp hq).2
        rw [hKt] at h2
        exact absurd h2 (by simp)
      · exact Bool.eq_false_of_ne_true hKt
    have hne : q ≠ c.kw := by
      intro e
      have hK2 : c.isK c.kw = false := e ▸ hK
      simp [Cfg.isK] at hK2
    rcases hm with hm | hm
    · obtain ⟨hmk, hsrc, hdst, -, hT4, -, -, -⟩ := pieceCands_mk q hq m hm
      have hrq : m.src < 64 ∧ m.dst < 64 ∧ m.src ≠ c.kw ∧ m.T ≤ 4 := by
        rw [hsrc]
        exact ⟨hqb, hdst, hne, hT4⟩
      have hps : m.pseudo.eval A = true → m.mv ∈ pseudo p ∧ m.KindOk p := by
        intro hpe
        rw [piece_pseudo hf hg hl q hq m hm] at hpe
        exact ⟨hpe.1, piece_kind hf q hq m hm hpe.1 hpe.2⟩
      rw [mkMove_legal hf hg hl m hmk hrq hps, Bool.and_eq_true] at h
      exact of_decide_eq_true h.2
    · obtain ⟨hmk, hsrc, hdst, hT, hpr, -, -⟩ := pawnCands_mk q hq m hm
      have hrq : m.src < 64 ∧ m.dst < 64 ∧ m.src ≠ c.kw ∧ m.T ≤ 4 := by
        rw [hsrc, hT]
        exact ⟨hqb, hdst, hne, Nat.zero_le 4⟩
      have hps : m.pseudo.eval A = true → m.mv ∈ pseudo p ∧ m.KindOk p := by
        intro hpe
        obtain ⟨hpsu, hkind, -⟩ := pawn_pseudo hf hg hl hr q hq m hm hpe
        exact ⟨hpsu, hkind⟩
      rw [mkMove_legal hf hg hl m hmk hrq hps, Bool.and_eq_true] at h
      exact of_decide_eq_true h.2
  · rw [king_legal hf hg hl m hm] at h
    exact of_decide_eq_true h
  · rw [castle_legal hf hg hl hr m hm] at h
    exact of_decide_eq_true h

theorem cand_chk (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hr : RightsOk c s r)
    (m : Cand) (hm : m ∈ c.cands r) (h : m.legal.eval A = true) : m.chk.eval A = givesCheck p m.mv := by
  rcases (mem_cands m).mp hm with ⟨q, hq, hm⟩ | hm | hm
  · have hqb : q < 64 := List.mem_range.mp (List.mem_filter.mp hq).1
    have hK : c.isK q = false := by
      by_cases hKt : c.isK q = true
      · have h2 := (List.mem_filter.mp hq).2
        rw [hKt] at h2
        exact absurd h2 (by simp)
      · exact Bool.eq_false_of_ne_true hKt
    have hne : q ≠ c.kw := by
      intro e
      have hK2 : c.isK c.kw = false := e ▸ hK
      simp [Cfg.isK] at hK2
    rcases hm with hm | hm
    · obtain ⟨hmk, hsrc, hdst, -, hT4, hpn, -, -⟩ := pieceCands_mk q hq m hm
      have hrq : m.src < 64 ∧ m.dst < 64 ∧ m.src ≠ c.kw ∧ m.T ≤ 4 := by
        rw [hsrc]
        exact ⟨hqb, hdst, hne, hT4⟩
      have hps : m.pseudo.eval A = true → m.mv ∈ pseudo p ∧ m.KindOk p := by
        intro hpe
        rw [piece_pseudo hf hg hl q hq m hm] at hpe
        exact ⟨hpe.1, piece_kind hf q hq m hm hpe.1 hpe.2⟩
      rw [mkMove_legal hf hg hl m hmk hrq hps, Bool.and_eq_true] at h
      have hpse : m.mv ∈ pseudo p ∧ p.board (toSq q) = some ⟨.white, kindOf m.T⟩ :=
        (piece_pseudo hf hg hl q hq m hm).mp h.1
      have hpr : ∀ k, m.promo = some k → m.T = 0 ∧ 1 ≤ k ∧ k ≤ 4 := by
        intro k hk
        rw [hpn] at hk
        cases hk
      have hpiece : p.board (toSq m.src) = some ⟨.white, kindOf m.T⟩ := by
        rw [hsrc]
        exact hpse.2
      exact mkMove_chk hf hg hl m hmk hrq hpse.1 (piece_kind hf q hq m hm hpse.1 hpse.2) hpiece hpr
    · obtain ⟨hmk, hsrc, hdst, hT, hpr, -, -⟩ := pawnCands_mk q hq m hm
      have hrq : m.src < 64 ∧ m.dst < 64 ∧ m.src ≠ c.kw ∧ m.T ≤ 4 := by
        rw [hsrc, hT]
        exact ⟨hqb, hdst, hne, Nat.zero_le 4⟩
      have hps : m.pseudo.eval A = true → m.mv ∈ pseudo p ∧ m.KindOk p := by
        intro hpe
        obtain ⟨hpsu, hkind, -⟩ := pawn_pseudo hf hg hl hr q hq m hm hpe
        exact ⟨hpsu, hkind⟩
      rw [mkMove_legal hf hg hl m hmk hrq hps, Bool.and_eq_true] at h
      obtain ⟨hpse, hkind, hb⟩ := pawn_pseudo hf hg hl hr q hq m hm h.1
      have hkind0 : kindOf 0 = .pawn := rfl
      have hpiece : p.board (toSq m.src) = some ⟨.white, kindOf m.T⟩ := by
        rw [hsrc, hT, hkind0]
        exact hb
      have hpr2 : ∀ k, m.promo = some k → m.T = 0 ∧ 1 ≤ k ∧ k ≤ 4 := fun k hk => ⟨hT, hpr k hk⟩
      exact mkMove_chk hf hg hl m hmk hrq hpse hkind hpiece hpr2
  · have hlg : m.mv ∈ legalMoves p := by
      rw [king_legal hf hg hl m hm] at h
      exact of_decide_eq_true h
    exact king_chk hf hg hl m hm hlg
  · have hlg : m.mv ∈ legalMoves p := by
      rw [castle_legal hf hg hl hr m hm] at h
      exact of_decide_eq_true h
    exact castle_chk hf hg hl hr m hm hlg

theorem any_congr {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self, ih fun a ha => h a (List.mem_cons_of_mem x ha)]

theorem map_congr_mem {α β : Type} {f g : α → β} (l : List α) (h : ∀ a ∈ l, f a = g a) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons, h x List.mem_cons_self, ih fun a ha => h a (List.mem_cons_of_mem x ha)]

theorem ray_eq_of_empty {b₁ b₂ : Board} (h : ∀ t, empty b₁ t = empty b₂ t) (n : Nat) (s : Sq)
    (df dr : Int) : ray b₁ s df dr n = ray b₂ s df dr n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [ray, ray]
    split
    · rfl
    · next t ht =>
      rw [h t]
      split
      · rw [ih t]
      · rfl

theorem rays_eq_of_empty {b₁ b₂ : Board} (h : ∀ t, empty b₁ t = empty b₂ t) (s : Sq)
    (ds : List (Int × Int)) : rays b₁ s ds = rays b₂ s ds := by
  unfold rays
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    show ray b₁ s d.1 d.2 7 ++ List.flatMap (fun (df, dr) => ray b₁ s df dr 7) ds =
      ray b₂ s d.1 d.2 7 ++ List.flatMap (fun (df, dr) => ray b₂ s df dr 7) ds
    rw [ray_eq_of_empty h 7 s d.1 d.2, ih]

theorem attacks_eq_of_empty {b₁ b₂ : Board} (h : ∀ t, empty b₁ t = empty b₂ t) (s : Sq) (q : Piece) :
    attacks b₁ s q = attacks b₂ s q := by
  obtain ⟨col, k⟩ := q
  cases k with
  | bishop =>
    show rays b₁ s bishopD = rays b₂ s bishopD
    exact rays_eq_of_empty h s bishopD
  | rook =>
    show rays b₁ s rookD = rays b₂ s rookD
    exact rays_eq_of_empty h s rookD
  | queen =>
    show rays b₁ s queenD = rays b₂ s queenD
    exact rays_eq_of_empty h s queenD
  | _ => rfl

theorem inCheckB_congr {b₁ b₂ : Board} {c : Color}
    (he : ∀ u, empty b₁ u = empty b₂ u)
    (h : ∀ u, b₁ u = b₂ u ∨ ∃ pc₁ pc₂, b₁ u = some pc₁ ∧ b₂ u = some pc₂ ∧
        pc₁.color ≠ c.opp ∧ pc₂.color ≠ c.opp ∧ pc₁.kind ≠ .king ∧ pc₂.kind ≠ .king) :
    (allSq.any fun t => b₁ t == some ⟨c, .king⟩ && attacked b₁ t c.opp) =
      (allSq.any fun t => b₂ t == some ⟨c, .king⟩ && attacked b₂ t c.opp) := by
  have hatt : ∀ u, attacked b₁ u c.opp = attacked b₂ u c.opp := by
    intro u
    show (allSq.any fun w => match b₁ w with
        | some pc => (pc.color == c.opp) && (attacks b₁ w pc).contains u
        | none => false) =
      (allSq.any fun w => match b₂ w with
        | some pc => (pc.color == c.opp) && (attacks b₂ w pc).contains u
        | none => false)
    apply any_congr
    intro w _
    rcases h w with hw | ⟨pc₁, pc₂, h1, h2, hno1, hno2, -, -⟩
    · rw [hw]
      cases h2 : b₂ w with
      | none => rfl
      | some pc =>
        show (pc.color == c.opp && (attacks b₁ w pc).contains u) = (pc.color == c.opp && (attacks b₂ w pc).contains u)
        rw [attacks_eq_of_empty he w]
    · rw [h1, h2]
      show (pc₁.color == c.opp && (attacks b₁ w pc₁).contains u) =
        (pc₂.color == c.opp && (attacks b₂ w pc₂).contains u)
      rw [beq_eq_false_iff_ne.mpr hno1, beq_eq_false_iff_ne.mpr hno2]
      rfl
  apply any_congr
  intro u _
  rw [hatt u]
  rcases h u with hu | ⟨pc₁, pc₂, h1, h2, -, -, hkn1, hkn2⟩
  · rw [hu]
  · rw [h1, h2]
    have f1 : ((some pc₁ : Option Piece) == some ⟨c, Kind.king⟩) = false := by
      rw [beq_eq_false_iff_ne]
      intro hc2
      exact hkn1 (congrArg Piece.kind (Option.some.inj hc2))
    have f2 : ((some pc₂ : Option Piece) == some ⟨c, Kind.king⟩) = false := by
      rw [beq_eq_false_iff_ne]
      intro hc2
      exact hkn2 (congrArg Piece.kind (Option.some.inj hc2))
    rw [f1, f2]

theorem inCheck_play_promo (p : Pos) (s t : Sq) (k₁ k₂ : Kind) (c : Color)
    (hk₁ : k₁ ≠ .king) (hk₂ : k₂ ≠ .king) (col : Color) (hbs : p.board s = some ⟨col, .pawn⟩)
    (hcol : col ≠ c.opp) :
    inCheck (play p ⟨s, t, some k₁⟩) c = inCheck (play p ⟨s, t, some k₂⟩) c := by
  have hisC1 : isCastle p ⟨s, t, some k₁⟩ = false := by
    unfold isCastle
    rw [hbs]
    rfl
  have hisC2 : isCastle p ⟨s, t, some k₂⟩ = false := by
    unfold isCastle
    rw [hbs]
    rfl
  by_cases hep : isEp p ⟨s, t, some k₁⟩ = true
  · have e1 := play_board_ep p ⟨s, t, some k₁⟩ hep
    have e2 := play_board_ep p ⟨s, t, some k₂⟩ hep
    have hbd : ∀ u : Sq, u ≠ t → (play p ⟨s,t,some k₁⟩).board u = (play p ⟨s,t,some k₂⟩).board u := by
      intro u hu
      rw [e1 u, e2 u, if_neg hu, if_neg hu]
      rfl
    have hb1 : (play p ⟨s,t,some k₁⟩).board t = some ⟨col, k₁⟩ := by
      rw [e1 t, if_pos rfl]
      show moved p ⟨s, t, some k₁⟩ = _
      rw [moved, hbs]
      rfl
    have hb2 : (play p ⟨s,t,some k₂⟩).board t = some ⟨col, k₂⟩ := by
      rw [e2 t, if_pos rfl]
      show moved p ⟨s, t, some k₂⟩ = _
      rw [moved, hbs]
      rfl
    refine inCheckB_congr ?_ ?_
    · intro u
      by_cases hut : u = t
      · subst hut
        show ((play p ⟨s, u, some k₁⟩).board u).isNone = ((play p ⟨s, u, some k₂⟩).board u).isNone
        rw [hb1, hb2]
        rfl
      · show ((play p ⟨s, t, some k₁⟩).board u).isNone = ((play p ⟨s, t, some k₂⟩).board u).isNone
        rw [hbd u hut]
    · intro u
      by_cases hut : u = t
      · subst hut
        exact Or.inr ⟨⟨col, k₁⟩, ⟨col, k₂⟩, hb1, hb2, hcol, hcol, hk₁, hk₂⟩
      · exact Or.inl (hbd u hut)
  · have hep1 : isEp p ⟨s, t, some k₁⟩ = false := Bool.eq_false_of_ne_true hep
    have hep2 : isEp p ⟨s, t, some k₂⟩ = false := hep1
    have e1 := play_board_simple p ⟨s, t, some k₁⟩ hisC1 hep1
    have e2 := play_board_simple p ⟨s, t, some k₂⟩ hisC2 hep2
    have hbd : ∀ u : Sq, u ≠ t → (play p ⟨s,t,some k₁⟩).board u = (play p ⟨s,t,some k₂⟩).board u := by
      intro u hu
      rw [e1 u, e2 u, if_neg hu, if_neg hu]
    have hb1 : (play p ⟨s,t,some k₁⟩).board t = some ⟨col, k₁⟩ := by
      rw [e1 t, if_pos rfl]
      show moved p ⟨s, t, some k₁⟩ = _
      rw [moved, hbs]
      rfl
    have hb2 : (play p ⟨s,t,some k₂⟩).board t = some ⟨col, k₂⟩ := by
      rw [e2 t, if_pos rfl]
      show moved p ⟨s, t, some k₂⟩ = _
      rw [moved, hbs]
      rfl
    refine inCheckB_congr ?_ ?_
    · intro u
      by_cases hut : u = t
      · subst hut
        show ((play p ⟨s, u, some k₁⟩).board u).isNone = ((play p ⟨s, u, some k₂⟩).board u).isNone
        rw [hb1, hb2]
        rfl
      · show ((play p ⟨s, t, some k₁⟩).board u).isNone = ((play p ⟨s, t, some k₂⟩).board u).isNone
        rw [hbd u hut]
    · intro u
      by_cases hut : u = t
      · subst hut
        exact Or.inr ⟨⟨col, k₁⟩, ⟨col, k₂⟩, hb1, hb2, hcol, hcol, hk₁, hk₂⟩
      · exact Or.inl (hbd u hut)

theorem mem_squares {q : Nat} (hq : q < 64) (h1 : q ≠ c.kw) (h2 : q ≠ c.kb) : q ∈ c.squares := by
  show q ∈ (List.range 64).filter fun q => !c.isK q
  refine List.mem_filter.mpr ⟨List.mem_range.mpr hq, ?_⟩
  show (!((q == c.kw) || (q == c.kb))) = true
  rw [nat_beq_of_ne _ _ h1, nat_beq_of_ne _ _ h2]
  rfl

theorem mem_targets_knight (q t : Nat) (hk : t ∈ knightL q) (hK : c.isK t = false) :
    t ∈ c.targets q 1 := by
  show t ∈ (knightL q).filter fun t => !c.isK t
  exact List.mem_filter.mpr ⟨hk, by rw [hK]; rfl⟩

theorem mem_targets_diag (q t : Nat) (hq : q < 64) (ht : t < 64) (hK : c.isK t = false)
    (hd : ∃ d ∈ diag, direction q t = some d) : t ∈ c.targets q 2 := by
  show t ∈ (diag.flatMap (rayL q)).filter fun t => !c.isK t
  obtain ⟨d, hd, hdir⟩ := hd
  exact List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨d, hd,
    (mem_rayL_iff q t hq ht d (List.mem_append.mpr (Or.inr hd))).mpr hdir⟩, by rw [hK]; rfl⟩

theorem mem_targets_orth (q t : Nat) (hq : q < 64) (ht : t < 64) (hK : c.isK t = false)
    (hd : ∃ d ∈ orth, direction q t = some d) : t ∈ c.targets q 3 := by
  show t ∈ (orth.flatMap (rayL q)).filter fun t => !c.isK t
  obtain ⟨d, hd, hdir⟩ := hd
  exact List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨d, hd,
    (mem_rayL_iff q t hq ht d (List.mem_append.mpr (Or.inl hd))).mpr hdir⟩, by rw [hK]; rfl⟩

theorem mem_targets_qd (q t : Nat) (hq : q < 64) (ht : t < 64) (hK : c.isK t = false)
    (hd : ∃ d ∈ orth ++ diag, direction q t = some d) : t ∈ c.targets q 4 := by
  show t ∈ ((orth ++ diag).flatMap (rayL q)).filter fun t => !c.isK t
  obtain ⟨d, hd, hdir⟩ := hd
  exact List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨d, hd,
    (mem_rayL_iff q t hq ht d hd).mpr hdir⟩, by rw [hK]; rfl⟩

def Cfg.pieceCand (c : Cfg) (q t T : Nat) : Cand :=
  c.mkMove q t none T (if T == 1 then Ex.and [c.p q T, Ex.not (c.wocc t)]
      else Ex.and [c.p q T, c.clear q t [] [], Ex.not (c.wocc t)]) none 1

theorem pieceCand_src (c : Cfg) (q t T : Nat) : (c.pieceCand q t T).src = q := rfl

theorem pieceCand_dst (c : Cfg) (q t T : Nat) : (c.pieceCand q t T).dst = t := rfl

theorem pieceCand_T (c : Cfg) (q t T : Nat) : (c.pieceCand q t T).T = T := rfl

theorem pieceCand_mv (c : Cfg) (q t T : Nat) :
    (c.pieceCand q t T).mv = ⟨toSq q, toSq t, none⟩ := rfl

theorem mem_pieceCands_pieceCand (q t T : Nat) (hT14 : 1 ≤ T ∧ T ≤ 4) (htg : t ∈ c.targets q T) :
    c.pieceCand q t T ∈ c.pieceCands q := by
  show _ ∈ [1, 2, 3, 4].flatMap fun T' => (c.targets q T').map fun t' =>
      c.mkMove q t' none T' (if T' == 1 then Ex.and [c.p q T', Ex.not (c.wocc t')]
        else Ex.and [c.p q T', c.clear q t' [] [], Ex.not (c.wocc t')]) none 1
  refine List.mem_flatMap.mpr ⟨T, ?_, List.mem_map.mpr ⟨t, htg, rfl⟩⟩
  rcases (show T = 1 ∨ T = 2 ∨ T = 3 ∨ T = 4 from by omega) with rfl | rfl | rfl | rfl <;> decide

theorem complete_piece_of_targets (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (mv : Move)
    (h : mv ∈ legalMoves p) (hps : mv ∈ pseudo p) (hpn : mv.promo = none)
    (T : Nat) (hT14 : 1 ≤ T ∧ T ≤ 4)
    (hbT : p.board mv.src = some ⟨.white, kindOf T⟩)
    (hqsq : mv.src.val ∈ c.squares) (hqw : mv.src.val ≠ c.kw)
    (htg : mv.dst.val ∈ c.targets mv.src.val T) :
    ∃ m ∈ c.cands r, m.legal.eval A = true ∧ mv ∈ m.covers := by
  have hq64 : mv.src.val < 64 := mv.src.isLt
  have ht64 : mv.dst.val < 64 := mv.dst.isLt
  have hmk : (c.pieceCand mv.src.val mv.dst.val T).IsMk c :=
    mkMove_IsMk _ _ _ _ _ _ _
  have hmpc : c.pieceCand mv.src.val mv.dst.val T ∈ c.pieceCands mv.src.val :=
    mem_pieceCands_pieceCand _ _ _ hT14 htg
  have hboard : p.board (toSq mv.src.val) = some ⟨.white, kindOf (c.pieceCand mv.src.val mv.dst.val T).T⟩ := by
    rw [toSq_val, pieceCand_T]
    exact hbT
  have hpsf : (c.pieceCand mv.src.val mv.dst.val T).pseudo.eval A = true →
      (c.pieceCand mv.src.val mv.dst.val T).mv ∈ pseudo p ∧
        (c.pieceCand mv.src.val mv.dst.val T).KindOk p := by
    intro hpe
    rw [piece_pseudo hf hg hl _ hqsq _ hmpc] at hpe
    exact ⟨hpe.1, piece_kind hf _ hqsq _ hmpc hpe.1 hpe.2⟩
  have hmv : (c.pieceCand mv.src.val mv.dst.val T).mv = mv := by
    rw [pieceCand_mv]
    show (⟨toSq mv.src.val, toSq mv.dst.val, none⟩ : Move) = mv
    rw [toSq_val, toSq_val, ← hpn]
  have hpsev : (c.pieceCand mv.src.val mv.dst.val T).pseudo.eval A = true :=
    (piece_pseudo hf hg hl _ hqsq _ hmpc).mpr ⟨by rw [hmv]; exact hps, hboard⟩
  have hrq : (c.pieceCand mv.src.val mv.dst.val T).src < 64 ∧
      (c.pieceCand mv.src.val mv.dst.val T).dst < 64 ∧
      (c.pieceCand mv.src.val mv.dst.val T).src ≠ c.kw ∧
      (c.pieceCand mv.src.val mv.dst.val T).T ≤ 4 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show mv.src.val < 64; exact hq64
    · show mv.dst.val < 64; exact ht64
    · show mv.src.val ≠ c.kw; exact hqw
    · show T ≤ 4; exact hT14.2
  have hleg : (c.pieceCand mv.src.val mv.dst.val T).legal.eval A = true := by
    rw [mkMove_legal hf hg hl _ hmk hrq hpsf, Bool.and_eq_true]
    exact ⟨hpsev, by rw [hmv]; exact decide_eq_true h⟩
  have hcovers : mv ∈ (c.pieceCand mv.src.val mv.dst.val T).covers := by
    rw [show (c.pieceCand mv.src.val mv.dst.val T).covers = [(c.pieceCand mv.src.val mv.dst.val T).mv]
      from by simp [Cand.covers, show (c.pieceCand mv.src.val mv.dst.val T).w = 1 from rfl]]
    exact List.mem_singleton.mpr hmv.symm
  exact ⟨_, (mem_cands _).mpr (Or.inl ⟨mv.src.val, hqsq, Or.inl hmpc⟩), hleg, hcovers⟩

theorem complete_piece (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (mv : Move) (h : mv ∈ legalMoves p)
    (hk : ∃ k, p.board mv.src = some ⟨.white, k⟩ ∧ k ≠ .pawn ∧ k ≠ .king) :
    ∃ m ∈ c.cands r, m.legal.eval A = true ∧ mv ∈ m.covers := by
  obtain ⟨k, hbk, hkp, hkk⟩ := hk
  have hturn : p.turn = .white := hf.2.1
  have hps : mv ∈ pseudo p := (mem_legalMoves h).1
  rcases pseudo_cases hps with ⟨s', q', hbs, hcol, hpm⟩ | hcm
  · have hsrc : mv.src = s' := move_src_of_pieceMoves hpm
    subst hsrc
    rw [hbk] at hbs
    obtain rfl := (Option.some.inj hbs).symm
    rcases pieceMoves_cases hpm with ⟨hkpp, -⟩ | ⟨-, -, hpn, hdst⟩
    · exact absurd hkpp hkp
    · have hatt : mv.dst ∈ attacks p.board mv.src ⟨.white, k⟩ := (List.mem_filter.mp hdst).1
      obtain ⟨hwk, hbkk, -⟩ := fits_kings hf
      have hqw : mv.src.val ≠ c.kw := by
        intro e
        rw [← e, toSq_val] at hwk
        rw [hbk] at hwk
        exact hkk (congrArg Piece.kind (Option.some.inj hwk))
      have hqb : mv.src.val ≠ c.kb := by
        intro e
        rw [← e, toSq_val] at hbkk
        rw [hbk] at hbkk
        have e9 := Option.some.inj hbkk
        simp only [Piece.mk.injEq] at e9
        exact absurd e9.1 (by decide)
      have htw : mv.dst.val ≠ c.kw := by
        intro e
        rw [← e, toSq_val] at hwk
        exact absurd hturn.symm (pseudo_dst hps _ hwk)
      have htb : mv.dst.val ≠ c.kb := by
        intro e
        rw [← e, toSq_val] at hbkk
        have hnk := pseudo_no_king_capture hf.1 hps
        rw [hturn] at hnk
        exact hnk (by exact hbkk)
      have hKt : c.isK mv.dst.val = false := by
        unfold Cfg.isK
        rw [nat_beq_of_ne _ _ htw, nat_beq_of_ne _ _ htb]
        rfl
      have hqsq : mv.src.val ∈ c.squares := mem_squares mv.src.isLt hqw hqb
      cases k with
      | pawn => exact absurd rfl hkp
      | king => exact absurd rfl hkk
      | knight =>
        have hd1 := (mem_attacks_knight p.board mv.src mv.dst .white).mp hatt
        exact complete_piece_of_targets hf hg hl mv h hps hpn 1 ⟨by decide, by decide⟩ hbk hqsq hqw
          (mem_targets_knight _ _ hd1 hKt)
      | bishop =>
        obtain ⟨d, hdir, ⟨-, hdia⟩, -⟩ :=
          (mem_attacks_slider p.board mv.src mv.dst ⟨.white, .bishop⟩ (Or.inl rfl)).mp hatt
        exact complete_piece_of_targets hf hg hl mv h hps hpn 2 ⟨by decide, by decide⟩ hbk hqsq hqw
          (mem_targets_diag _ _ mv.src.isLt mv.dst.isLt hKt ⟨d, hdia rfl, hdir⟩)
      | rook =>
        obtain ⟨d, hdir, ⟨hor, -⟩, -⟩ :=
          (mem_attacks_slider p.board mv.src mv.dst ⟨.white, .rook⟩ (Or.inr (Or.inl rfl))).mp hatt
        exact complete_piece_of_targets hf hg hl mv h hps hpn 3 ⟨by decide, by decide⟩ hbk hqsq hqw
          (mem_targets_orth _ _ mv.src.isLt mv.dst.isLt hKt ⟨d, hor rfl, hdir⟩)
      | queen =>
        obtain ⟨d, hdir, -, -⟩ :=
          (mem_attacks_slider p.board mv.src mv.dst ⟨.white, .queen⟩ (Or.inr (Or.inr rfl))).mp hatt
        exact complete_piece_of_targets hf hg hl mv h hps hpn 4 ⟨by decide, by decide⟩ hbk hqsq hqw
          (mem_targets_qd _ _ mv.src.isLt mv.dst.isLt hKt ⟨d, direction_mem hdir, hdir⟩)
  · obtain ⟨hsrc, -, hb2, -, -⟩ := castleMoves_cases hcm
    rw [hsrc, hb2] at hbk
    exact absurd (congrArg Piece.kind (Option.some.inj hbk)).symm hkk


theorem fr2_rank (x : Sq) : (fr x.val).2 = ((x.rank : Nat) : Int) := by
  rw [fr_snd x.isLt, toSq_val]

theorem not_isK_of_none (hf : Fits c p) (x : Nat) (hx : p.board (toSq x) = none) : c.isK x = false := by
  obtain ⟨hwk, hbkk, -⟩ := fits_kings hf
  unfold Cfg.isK
  have h1 : (x == c.kw) = false := by
    rw [beq_eq_false_iff_ne]
    intro e
    rw [← e] at hwk
    rw [hx] at hwk
    exact absurd hwk (by simp)
  have h2 : (x == c.kb) = false := by
    rw [beq_eq_false_iff_ne]
    intro e
    rw [← e] at hbkk
    rw [hx] at hbkk
    exact absurd hbkk (by simp)
  rw [h1, h2]
  rfl

theorem not_isK_of_board (hf : Fits c p) (x : Nat) (pc : Piece)
    (hx : p.board (toSq x) = some pc) (hw : pc ≠ ⟨.white, .king⟩) (hb : pc ≠ ⟨.black, .king⟩) :
    c.isK x = false := by
  obtain ⟨hwk, hbkk, -⟩ := fits_kings hf
  unfold Cfg.isK
  have h1 : (x == c.kw) = false := beq_eq_false_iff_ne.mpr (by
    intro e
    rw [← e, hx] at hwk
    exact hw (Option.some.inj hwk))
  have h2 : (x == c.kb) = false := beq_eq_false_iff_ne.mpr (by
    intro e
    rw [← e, hx] at hbkk
    exact hb (Option.some.inj hbkk))
  rw [h1, h2]
  rfl

theorem mem_mkPawn_single {q tv : Nat} (ps : Ex) (h7 : ((fr tv).2 == 7) = false) :
    c.mkMove q tv none 0 ps none 1 ∈ c.mkPawn q tv ps := by
  simp only [Cfg.mkPawn]
  rw [h7]
  simp only [Bool.false_eq_true, ite_false]
  exact List.mem_singleton_self _

theorem mem_mkPawn_promo1 {q tv : Nat} (ps : Ex) (h7 : ((fr tv).2 == 7) = true) :
    c.mkMove q tv (some 1) 0 ps none 4 ∈ c.mkPawn q tv ps := by
  simp only [Cfg.mkPawn]
  rw [if_pos h7]
  exact List.mem_map.mpr ⟨(1, 4), by decide, rfl⟩

theorem mem_pawnCands_push1 {q tv : Nat}
    (hrk : ((fr q).2 == 0 || (fr q).2 == 7) = false)
    (ht : sqo (fr q).1 ((fr q).2 + 1) = some tv) (hKt : c.isK tv = false)
    {z : Cand} (hz : z ∈ c.mkPawn q tv (.and [c.p q 0, c.empty tv])) :
    z ∈ c.pawnCands r q := by
  simp only [Cfg.pawnCands]
  rw [hrk]
  simp only [Bool.false_eq_true, ite_false]
  rw [ht, Option.getD_some, hKt]
  simp only [Bool.false_eq_true, ite_false]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hz)))

theorem mem_pawnCands_push2 {q tv t3v : Nat}
    (hrk : ((fr q).2 == 0 || (fr q).2 == 7) = false)
    (ht : sqo (fr q).1 ((fr q).2 + 1) = some tv) (hKt : c.isK tv = false)
    (ht3 : sqo (fr q).1 3 = some t3v) (hKt3 : c.isK t3v = false) (hr1 : (fr q).2 = 1)
    {z : Cand} (hz : z ∈ c.mkPawn q t3v (.and [c.p q 0, c.empty tv, c.empty t3v])) :
    z ∈ c.pawnCands r q := by
  simp only [Cfg.pawnCands]
  rw [hrk]
  simp only [Bool.false_eq_true, ite_false]
  rw [ht, Option.getD_some, ht3, Option.getD_some, hKt, hKt3]
  simp only [Bool.false_eq_true, ite_false]
  rw [hr1]
  simp only [beq_self_eq_true, Bool.true_and]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hz)))

theorem mem_pawnCands_cap {q tv : Nat} {df : Int}
    (hrk : ((fr q).2 == 0 || (fr q).2 == 7) = false)
    (hdf : df ∈ [(-1 : Int), 1])
    (ht : sqo ((fr q).1 + df) ((fr q).2 + 1) = some tv) (hKt : c.isK tv = false)
    {z : Cand} (hz : z ∈ c.mkPawn q tv (.and [c.p q 0, c.has tv symB])) :
    z ∈ c.pawnCands r q := by
  simp only [Cfg.pawnCands]
  rw [hrk]
  simp only [Bool.false_eq_true, ite_false]
  apply List.mem_append.mpr; right
  refine List.mem_flatMap.mpr ⟨df, hdf, ?_⟩
  rw [ht]
  show z ∈ (if c.isK tv = true then [] else c.mkPawn q tv (.and [c.p q 0, c.has tv symB]) ++
    (match (if ((fr q).2 == 4) = true then r.ep.lookup ((fr q).1 + df).toNat else none) with
     | some v => [c.mkMove q tv none 0 (.and [c.p q 0, .v v]) (sqo ((fr q).1 + df) 4) 1]
     | none => []))
  rw [hKt]
  simp only [Bool.false_eq_true, ite_false]
  exact List.mem_append.mpr (Or.inl hz)

theorem mem_pawnCands_ep {q tv : Nat} {df : Int}
    (hrk : ((fr q).2 == 0 || (fr q).2 == 7) = false)
    (hdf : df ∈ [(-1 : Int), 1])
    (ht : sqo ((fr q).1 + df) ((fr q).2 + 1) = some tv) (hKt : c.isK tv = false)
    (hr4 : (fr q).2 = 4) (v : Int) (hlk : r.ep.lookup ((fr q).1 + df).toNat = some v) :
    c.mkMove q tv none 0 (.and [c.p q 0, .v v]) (sqo ((fr q).1 + df) 4) 1 ∈ c.pawnCands r q := by
  simp only [Cfg.pawnCands]
  rw [hrk]
  simp only [Bool.false_eq_true, ite_false]
  apply List.mem_append.mpr; right
  refine List.mem_flatMap.mpr ⟨df, hdf, ?_⟩
  rw [ht]
  show _ ∈ (if c.isK tv = true then [] else c.mkPawn q tv (.and [c.p q 0, c.has tv symB]) ++
    (match (if ((fr q).2 == 4) = true then r.ep.lookup ((fr q).1 + df).toNat else none) with
     | some v => [c.mkMove q tv none 0 (.and [c.p q 0, .v v]) (sqo ((fr q).1 + df) 4) 1]
     | none => []))
  rw [hKt]
  simp only [Bool.false_eq_true, ite_false]
  apply List.mem_append.mpr; right
  rw [hr4]
  simp only [beq_self_eq_true, ite_true, hlk]
  exact List.mem_singleton_self _

theorem pawnMoves_white_cases {p : Pos} {s : Sq} {m : Move} (h : m ∈ pawnMoves p s .white) :
    (∃ t, off s 0 1 = some t ∧ empty p.board t = true ∧
        (if t.rank == 7 then ∃ k, k ∈ [Kind.knight, .bishop, .rook, .queen] ∧ m = ⟨s, t, some k⟩
         else m = ⟨s, t, none⟩)) ∨
    (∃ t, t ∈ steps s [(1, 1), (-1, 1)] ∧ (foe p.board .white t = true ∨ epCap p .white t = true) ∧
        (if t.rank == 7 then ∃ k, k ∈ [Kind.knight, .bishop, .rook, .queen] ∧ m = ⟨s, t, some k⟩
         else m = ⟨s, t, none⟩)) ∨
    (∃ t, s.rank = 1 ∧ (∃ u, off s 0 1 = some u ∧ empty p.board u = true) ∧
        off s 0 2 = some t ∧ empty p.board t = true ∧ m = ⟨s, t, none⟩) :=
  pawnMoves_cases h

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons x xs ih =>
    obtain ⟨k, b'⟩ := x
    rw [List.lookup_cons] at h
    split at h
    · next hkk =>
      rcases beq_iff_eq.mp hkk
      rcases Option.some.inj h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem complete_pawn_aux (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hr : RightsOk c s r)
    (mv : Move) (h : mv ∈ legalMoves p) (hps : mv ∈ pseudo p)
    (hk : p.board mv.src = some ⟨.white, .pawn⟩)
    (tv : Nat) (psy : Ex) (epr : Option Nat) (w : Nat) (pr : Option Nat)
    (htv : tv < 64)
    (hpc : c.mkMove mv.src.val tv pr 0 psy epr w ∈ c.pawnCands r mv.src.val)
    (hpsv : psy.eval A = true)
    (hmvl : (c.mkMove mv.src.val tv pr 0 psy epr w).mv ∈ legalMoves p)
    (hcov : mv ∈ (c.mkMove mv.src.val tv pr 0 psy epr w).covers) :
    ∃ m ∈ c.cands r, m.legal.eval A = true ∧ mv ∈ m.covers := by
  obtain ⟨hwk, hbkk, -⟩ := fits_kings hf
  have hq64 : mv.src.val < 64 := mv.src.isLt
  have hqw : mv.src.val ≠ c.kw := by
    intro e
    rw [← e, toSq_val] at hwk
    rw [hk] at hwk
    exact absurd (congrArg Piece.kind (Option.some.inj hwk)) (by decide)
  have hqb : mv.src.val ≠ c.kb := by
    intro e
    rw [← e, toSq_val] at hbkk
    rw [hk] at hbkk
    have e9 := Option.some.inj hbkk
    simp only [Piece.mk.injEq] at e9
    exact absurd e9.1 (by decide)
  have hqsq : mv.src.val ∈ c.squares := mem_squares hq64 hqw hqb
  have hmk : Cand.IsMk c (c.mkMove mv.src.val tv pr 0 psy epr w) := mkMove_IsMk _ _ _ _ _ _ _
  have hpsf : (c.mkMove mv.src.val tv pr 0 psy epr w).pseudo.eval A = true →
      (c.mkMove mv.src.val tv pr 0 psy epr w).mv ∈ pseudo p ∧
        (c.mkMove mv.src.val tv pr 0 psy epr w).KindOk p := by
    intro hpe
    obtain ⟨h1, h2, -⟩ := pawn_pseudo hf hg hl hr _ hqsq _ hpc hpe
    exact ⟨h1, h2⟩
  have hrq : (c.mkMove mv.src.val tv pr 0 psy epr w).src < 64 ∧
      (c.mkMove mv.src.val tv pr 0 psy epr w).dst < 64 ∧
      (c.mkMove mv.src.val tv pr 0 psy epr w).src ≠ c.kw ∧
      (c.mkMove mv.src.val tv pr 0 psy epr w).T ≤ 4 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show mv.src.val < 64; exact hq64
    · show tv < 64; exact htv
    · show mv.src.val ≠ c.kw; exact hqw
    · show (0 : Nat) ≤ 4; exact Nat.zero_le 4
  have hleg : (c.mkMove mv.src.val tv pr 0 psy epr w).legal.eval A = true := by
    rw [mkMove_legal hf hg hl _ hmk hrq hpsf, Bool.and_eq_true]
    refine ⟨?_, decide_eq_true hmvl⟩
    show psy.eval A = true
    exact hpsv
  exact ⟨_, (mem_cands _).mpr (Or.inl ⟨_, hqsq, Or.inr hpc⟩), hleg, hcov⟩
theorem covers_promo_mem (q tv : Nat) (psy : Ex) (s' t' : Sq) (k : Kind)
    (hs : toSq q = s') (ht : toSq tv = t')
    (hk : k ∈ [Kind.knight, .bishop, .rook, .queen]) :
    (⟨s', t', some k⟩ : Move) ∈ (c.mkMove q tv (some 1) 0 psy none 4).covers := by
  show (⟨s', t', some k⟩ : Move) ∈ [Kind.knight, .bishop, .rook, .queen].map
    (fun k => (⟨toSq q, toSq tv, some k⟩ : Move))
  exact List.mem_map.mpr ⟨k, hk, by rw [hs, ht]⟩

theorem covers_single_mem (q tv : Nat) (psy : Ex) (epr : Option Nat) (s' t' : Sq)
    (hs : toSq q = s') (ht : toSq tv = t') :
    (⟨s', t', none⟩ : Move) ∈ (c.mkMove q tv none 0 psy epr 1).covers := by
  show (⟨s', t', none⟩ : Move) ∈ [(⟨toSq q, toSq tv, none⟩ : Move)]
  exact List.mem_singleton.mpr (by rw [hs, ht])

theorem complete_pawn (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hr : RightsOk c s r)
    (mv : Move) (h : mv ∈ legalMoves p) (hk : p.board mv.src = some ⟨.white, .pawn⟩) :
    ∃ m ∈ c.cands r, m.legal.eval A = true ∧ mv ∈ m.covers := by
  have hturn : p.turn = .white := hf.2.1
  have hA := hf.1
  have hps : mv ∈ pseudo p := (mem_legalMoves h).1
  obtain ⟨hwk, hbkk, -⟩ := fits_kings hf
  have hq64 : mv.src.val < 64 := mv.src.isLt
  have hqw : mv.src.val ≠ c.kw := by
    intro e
    rw [← e, toSq_val] at hwk
    rw [hk] at hwk
    exact absurd (congrArg Piece.kind (Option.some.inj hwk)) (by decide)
  have hqb : mv.src.val ≠ c.kb := by
    intro e
    rw [← e, toSq_val] at hbkk
    rw [hk] at hbkk
    have e9 := Option.some.inj hbkk
    simp only [Piece.mk.injEq] at e9
    exact absurd e9.1 (by decide)
  have hqsq : mv.src.val ∈ c.squares := mem_squares hq64 hqw hqb
  have hcol : (.white : Color) ≠ p.turn.opp := by rw [hturn]; decide
  have heP : (c.p mv.src.val 0).eval A = true := by
    rw [eval_p hf hg hl _ 0 hq64 (by decide)]
    show (symOf (p.board (toSq mv.src.val)) == 0) = true
    rw [toSq_val mv.src, hk]
    rfl
  have hrk : ((fr mv.src.val).2 == 0 || (fr mv.src.val).2 == 7) = false := by
    have e1 : (fr mv.src.val).2 ≠ 0 := by
      rw [fr2_rank mv.src]
      intro e
      apply hA.noBackPawn mv.src .white (Or.inl (show mv.src.rank = 0 from by omega)) hk
    have e7 : (fr mv.src.val).2 ≠ 7 := by
      rw [fr2_rank mv.src]
      intro e
      apply hA.noBackPawn mv.src .white (Or.inr (show mv.src.rank = 7 from by omega)) hk
    rw [beq_eq_false_iff_ne.mpr e1, beq_eq_false_iff_ne.mpr e7]
    rfl
  rcases pseudo_cases hps with ⟨s', q', hbs, hcol', hpm⟩ | hcm
  · have hsrc : mv.src = s' := move_src_of_pieceMoves hpm
    subst hsrc
    rw [hk] at hbs
    obtain rfl := (Option.some.inj hbs).symm
    rcases pieceMoves_cases hpm with ⟨-, hpw⟩ | ⟨hknp, -, -, -⟩
    · have hpw2 : mv ∈ pawnMoves p mv.src .white := hpw
      rcases pawnMoves_white_cases hpw2 with ⟨t', hof, hem, hmk⟩ | ⟨t', hst, hfe, hmk⟩ | ⟨t', hsr, ⟨u, hof1, he1⟩, hof2, he2, hm⟩
      · have hbn : p.board t' = none := board_none_of_empty hem
        have hsqo : sqo (fr mv.src.val).1 ((fr mv.src.val).2 + 1) = some t'.val := by
          have e := (off_sqo_some mv.src t' 0 1).mp hof
          rwa [Int.add_zero] at e
        have hKt' : c.isK t'.val = false := not_isK_of_none hf _ (by rw [toSq_val t']; exact hbn)
        by_cases hL : (t'.rank == 7) = true
        · simp only [hL, ite_true] at hmk
          obtain ⟨k', hkL, hmv'⟩ := hmk
          have hk4 : k' = .knight ∨ k' = .bishop ∨ k' = .rook ∨ k' = .queen := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hkL
            exact hkL
          have hknk' : k' ≠ .king := by rcases hk4 with rfl | rfl | rfl | rfl <;> decide
          have h7t : ((fr t'.val).2 == 7) = true := by
            rw [beq_iff_eq, fr2_rank, beq_iff_eq.mp hL]
            rfl
          have hpsv : (Ex.and [c.p mv.src.val 0, c.empty t'.val]).eval A = true := by
            rw [eval_and2, Bool.and_eq_true]
            exact ⟨heP, by rw [eval_empty hf hg hl _ t'.isLt, toSq_val t', hbn, Option.isNone_none]⟩
          have hmvl : (c.mkMove mv.src.val t'.val (some 1) 0 (.and [c.p mv.src.val 0, c.empty t'.val]) none 4).mv ∈ legalMoves p := by
            show (⟨toSq mv.src.val, toSq t'.val, some (kindOf 1)⟩ : Move) ∈ legalMoves p
            rw [toSq_val mv.src, toSq_val t', legalMoves, List.mem_filter]
            refine ⟨?_, ?_⟩
            · rw [show (⟨mv.src, t', some (kindOf 1)⟩ : Move) =
                  (c.mkMove mv.src.val t'.val (some 1) 0
                    (Ex.and [c.p mv.src.val 0, c.empty t'.val]) none 4).mv from by
                show (⟨mv.src, t', some (kindOf 1)⟩ : Move) =
                  ⟨toSq mv.src.val, toSq t'.val, some (kindOf 1)⟩
                rw [toSq_val mv.src, toSq_val t']]
              exact (pawn_pseudo hf hg hl hr mv.src.val hqsq _
                (mem_pawnCands_push1 hrk hsqo hKt' (mem_mkPawn_promo1 _ h7t)) hpsv).1
            · rw [Bool.not_eq_true']
              show inCheck (play p ⟨mv.src, t', some .knight⟩) p.turn = false
              rw [inCheck_play_promo p mv.src t' .knight k' p.turn (by decide) hknk' .white hk hcol]
              have h2 := (mem_legalMoves h).2
              rwa [hmv'] at h2
          have hcov : mv ∈ (c.mkMove mv.src.val t'.val (some 1) 0 (.and [c.p mv.src.val 0, c.empty t'.val]) none 4).covers := by
            rw [hmv']
            exact covers_promo_mem _ _ _ mv.src t' k' (toSq_val mv.src) (toSq_val t') hkL
          exact complete_pawn_aux hf hg hl hr mv h hps hk t'.val
            (.and [c.p mv.src.val 0, c.empty t'.val]) none 4 (some 1) t'.isLt
            (mem_pawnCands_push1 hrk hsqo hKt' (mem_mkPawn_promo1 _ h7t)) hpsv hmvl hcov
        · have ht7f : (t'.rank == 7) = false := by
            cases h2 : (t'.rank == 7) with
            | false => rfl
            | true => exact absurd h2 hL
          simp only [ht7f, ite_false] at hmk
          have h7f : ((fr t'.val).2 == 7) = false := by
            rw [beq_eq_false_iff_ne, fr2_rank]
            intro e
            have e2 : t'.rank = 7 := by
              have e3 := congrArg Int.toNat e
              rwa [Int.toNat_natCast, show Int.toNat (7 : Int) = 7 from rfl] at e3
            exact hL (beq_iff_eq.mpr e2)
          have hpsv : (Ex.and [c.p mv.src.val 0, c.empty t'.val]).eval A = true := by
            rw [eval_and2, Bool.and_eq_true]
            exact ⟨heP, by rw [eval_empty hf hg hl _ t'.isLt, toSq_val t', hbn, Option.isNone_none]⟩
          have hmvl : (c.mkMove mv.src.val t'.val none 0 (.and [c.p mv.src.val 0, c.empty t'.val]) none 1).mv ∈ legalMoves p := by
            show (⟨toSq mv.src.val, toSq t'.val, (none : Option Nat).map kindOf⟩ : Move) ∈ legalMoves p
            rw [Option.map_none, toSq_val mv.src, toSq_val t', ← hmk]
            exact h
          have hcov : mv ∈ (c.mkMove mv.src.val t'.val none 0 (.and [c.p mv.src.val 0, c.empty t'.val]) none 1).covers := by
            rw [hmk]
            exact covers_single_mem _ _ _ _ mv.src t' (toSq_val mv.src) (toSq_val t')
          exact complete_pawn_aux hf hg hl hr mv h hps hk t'.val
            (.and [c.p mv.src.val 0, c.empty t'.val]) none 1 none t'.isLt
            (mem_pawnCands_push1 hrk hsqo hKt' (mem_mkPawn_single _ h7f)) hpsv hmvl hcov
      · obtain ⟨d, hd, hoffd⟩ := steps_mem hst
        have hd2 : d = ((1 : Int), 1) ∨ d = (-1, 1) := by
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using hd
        have hdA : d.1 = (1 : Int) ∨ d.1 = -1 := by
          rcases hd2 with hd0 | hd0
          · exact Or.inl (congrArg Prod.fst hd0)
          · exact Or.inr (congrArg Prod.fst hd0)
        have hd2one : d.2 = 1 := by
          rcases hd2 with hd0 | hd0
          · exact congrArg Prod.snd hd0
          · exact congrArg Prod.snd hd0
        have hsqo : sqo ((fr mv.src.val).1 + d.1) ((fr mv.src.val).2 + 1) = some t'.val := by
          have e := (off_sqo_some mv.src t' d.1 d.2).mp hoffd
          rwa [hd2one] at e
        have hdf : d.1 ∈ [(-1 : Int), 1] := by
          rcases hdA with hd1 | hd1 <;> rw [hd1] <;> decide
        have hdstt : mv.dst = t' := by
          by_cases hL : (t'.rank == 7) = true
          · simp only [hL, ite_true] at hmk
            obtain ⟨k0, hkL0, hmv'⟩ := hmk
            exact congrArg Move.dst hmv'
          · have ht7f : (t'.rank == 7) = false := by
              cases h2 : (t'.rank == 7) with
              | false => rfl
              | true => exact absurd h2 hL
            simp only [ht7f, ite_false] at hmk
            exact congrArg Move.dst hmk
        have hnkc : p.board t' ≠ some ⟨.black, .king⟩ := by
          have hnk := pseudo_no_king_capture hA hps
          rw [hturn, hdstt] at hnk
          exact hnk
        rcases hfe with hfoe | hepc
        · cases hbt' : p.board t' with
          | none =>
            have e : foe p.board .white t' = false := by unfold foe; rw [hbt']
            rw [e] at hfoe
            simp at hfoe
          | some pc =>
            have efoc : foe p.board .white t' = (pc.color != .white) := by unfold foe; rw [hbt']
            rw [efoc] at hfoe
            have hpcol : pc.color ≠ .white := bne_iff_ne.mp hfoe
            obtain ⟨cpc, kpc⟩ := pc
            have hcb : cpc = .black := by
              cases cpc with
              | white =>
                have h2 : ((⟨.white, kpc⟩ : Piece).color) ≠ .white := hpcol
                exact absurd rfl h2
              | black => rfl
            have htw2 : t'.val ≠ c.kw := by
              intro e
              rw [← e, toSq_val t'] at hwk
              rw [hbt'] at hwk
              have e9 := Option.some.inj hwk
              simp only [Piece.mk.injEq] at e9
              exact absurd (e9.1.symm.trans hcb) (by decide)
            have htb2 : t'.val ≠ c.kb := by
              intro e
              rw [← e, toSq_val t'] at hbkk
              exact hnkc hbkk
            have hKt' : c.isK t'.val = false := by
              unfold Cfg.isK
              rw [nat_beq_of_ne _ _ htw2, nat_beq_of_ne _ _ htb2]
              rfl
            have heHas : (c.has t'.val symB).eval A = true := by
              rw [eval_has hf hg hl _ t'.isLt symB (by decide), toSq_val t', hbt']
              show (symB.contains (symOf (some ⟨cpc, kpc⟩))) = true
              subst hcb
              cases kpc with
              | king => exact absurd hbt' hnkc
              | pawn => rfl
              | knight => rfl
              | bishop => rfl
              | rook => rfl
              | queen => rfl
            by_cases hL : (t'.rank == 7) = true
            · simp only [hL, ite_true] at hmk
              obtain ⟨k', hkL, hmv'⟩ := hmk
              have hk4 : k' = .knight ∨ k' = .bishop ∨ k' = .rook ∨ k' = .queen := by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hkL
                exact hkL
              have hknk' : k' ≠ .king := by rcases hk4 with rfl | rfl | rfl | rfl <;> decide
              have h7t : ((fr t'.val).2 == 7) = true := by
                rw [beq_iff_eq, fr2_rank, beq_iff_eq.mp hL]
                rfl
              have hpsv : (Ex.and [c.p mv.src.val 0, c.has t'.val symB]).eval A = true := by
                rw [eval_and2, Bool.and_eq_true]
                exact ⟨heP, heHas⟩
              have hmvl : (c.mkMove mv.src.val t'.val (some 1) 0 (.and [c.p mv.src.val 0, c.has t'.val symB]) none 4).mv ∈ legalMoves p := by
                show (⟨toSq mv.src.val, toSq t'.val, some (kindOf 1)⟩ : Move) ∈ legalMoves p
                rw [toSq_val mv.src, toSq_val t', legalMoves, List.mem_filter]
                refine ⟨?_, ?_⟩
                · rw [show (⟨mv.src, t', some (kindOf 1)⟩ : Move) =
                    (c.mkMove mv.src.val t'.val (some 1) 0
                      (Ex.and [c.p mv.src.val 0, c.has t'.val symB]) none 4).mv from by
                  show (⟨mv.src, t', some (kindOf 1)⟩ : Move) =
                    ⟨toSq mv.src.val, toSq t'.val, some (kindOf 1)⟩
                  rw [toSq_val mv.src, toSq_val t']]
                  exact (pawn_pseudo hf hg hl hr mv.src.val hqsq _
                    (mem_pawnCands_cap hrk hdf hsqo hKt' (mem_mkPawn_promo1 _ h7t)) hpsv).1
                · rw [Bool.not_eq_true']
                  show inCheck (play p ⟨mv.src, t', some .knight⟩) p.turn = false
                  rw [inCheck_play_promo p mv.src t' .knight k' p.turn (by decide) hknk' .white hk hcol]
                  have h2 := (mem_legalMoves h).2
                  rwa [hmv'] at h2
              have hcov : mv ∈ (c.mkMove mv.src.val t'.val (some 1) 0 (.and [c.p mv.src.val 0, c.has t'.val symB]) none 4).covers := by
                rw [hmv']
                exact covers_promo_mem _ _ _ mv.src t' k' (toSq_val mv.src) (toSq_val t') hkL
              exact complete_pawn_aux hf hg hl hr mv h hps hk t'.val
                (.and [c.p mv.src.val 0, c.has t'.val symB]) none 4 (some 1) t'.isLt
                (mem_pawnCands_cap hrk hdf hsqo hKt' (mem_mkPawn_promo1 _ h7t)) hpsv hmvl hcov
            · have ht7f : (t'.rank == 7) = false := by
                cases h2 : (t'.rank == 7) with
                | false => rfl
                | true => exact absurd h2 hL
              simp only [ht7f, ite_false] at hmk
              have h7f : ((fr t'.val).2 == 7) = false := by
                rw [beq_eq_false_iff_ne, fr2_rank]
                intro e
                have e2 : t'.rank = 7 := by
                  have e3 := congrArg Int.toNat e
                  rwa [Int.toNat_natCast, show Int.toNat (7 : Int) = 7 from rfl] at e3
                exact hL (beq_iff_eq.mpr e2)
              have hpsv : (Ex.and [c.p mv.src.val 0, c.has t'.val symB]).eval A = true := by
                rw [eval_and2, Bool.and_eq_true]
                exact ⟨heP, heHas⟩
              have hmvl : (c.mkMove mv.src.val t'.val none 0 (.and [c.p mv.src.val 0, c.has t'.val symB]) none 1).mv ∈ legalMoves p := by
                show (⟨toSq mv.src.val, toSq t'.val, (none : Option Nat).map kindOf⟩ : Move) ∈ legalMoves p
                rw [Option.map_none, toSq_val mv.src, toSq_val t', ← hmk]
                exact h
              have hcov : mv ∈ (c.mkMove mv.src.val t'.val none 0 (.and [c.p mv.src.val 0, c.has t'.val symB]) none 1).covers := by
                rw [hmk]
                exact covers_single_mem _ _ _ _ mv.src t' (toSq_val mv.src) (toSq_val t')
              exact complete_pawn_aux hf hg hl hr mv h hps hk t'.val
                (.and [c.p mv.src.val 0, c.has t'.val symB]) none 1 none t'.isLt
                (mem_pawnCands_cap hrk hdf hsqo hKt' (mem_mkPawn_single _ h7f)) hpsv hmvl hcov
        · unfold epCap at hepc
          rw [Bool.and_eq_true, Bool.and_eq_true] at hepc
          obtain ⟨⟨hep1, hemt'⟩, hbehind⟩ := hepc
          have hepmv : p.ep = some t' := beq_iff_eq.mp hep1
          have hbn : p.board t' = none := board_none_of_empty hemt'
          have hEp := hA.ep t' hepmv
          unfold EpOk at hEp
          rw [hturn] at hEp
          dsimp only at hEp
          obtain ⟨hr5, hbp4, hbn2, hb6⟩ := hEp
          have ht7f : (t'.rank == 7) = false := by
            rw [beq_eq_false_iff_ne]
            intro e
            omega
          simp only [ht7f, ite_false] at hmk
          have hisEp : isEp p mv = true := by
            rw [hmk]
            show ((p.board mv.src).any (fun x => x.kind == .pawn) && (mv.src.file != t'.file) && empty p.board t') = true
            rw [Bool.and_eq_true, Bool.and_eq_true]
            refine ⟨⟨?_, ?_⟩, hemt'⟩
            · rw [hk]
              rfl
            · rw [bne_iff_ne]
              obtain ⟨e1, -⟩ := (off_eq_some mv.src t' d.1 d.2).mp hoffd
              rcases hdA with hd1 | hd1 <;> rw [hd1] at e1
              · intro e
                rw [e] at e1
                omega
              · intro e
                rw [e] at e1
                omega
          obtain ⟨hep2, hvic, hpn2, hrank⟩ := pseudo_ep hA hps hisEp
          rw [hdstt, hturn, show Color.white.fwd = 1 from rfl] at hrank
          have hsr4 : mv.src.rank = 4 := by omega
          have hr4 : (fr mv.src.val).2 = 4 := by
            rw [fr2_rank mv.src, hsr4]
            rfl
          have hff : ((fr mv.src.val).1 + d.1).toNat = t'.file := by
            have e1 := (sqo_fr hsqo).1
            rw [fr_fst t'.isLt, toSq_val t'] at e1
            rw [← e1]
            exact Int.toNat_natCast _
          have hf8 : ((fr mv.src.val).1 + d.1).toNat < 8 := by rw [hff]; exact file_lt t'
          have hsq5 : toSq (((fr mv.src.val).1 + d.1).toNat + 40) = t' := by
            apply Fin.ext
            show ((((fr mv.src.val).1 + d.1).toNat + 40) % 64 : Nat) = t'.val
            rw [hff, sq_val t', hr5, Nat.mod_eq_of_lt (by have := file_lt t'; omega)]
            omega
          have hsq4 : toSq (((fr mv.src.val).1 + d.1).toNat + 32) = sq t'.file 4 := by
            apply Fin.ext
            show ((((fr mv.src.val).1 + d.1).toNat + 32) % 64 : Nat) = (4 * 8 + t'.file) % 64
            rw [hff, Nat.mod_eq_of_lt (by have := file_lt t'; omega),
              Nat.mod_eq_of_lt (by have := file_lt t'; omega)]
            omega
          have hsq6 : toSq (((fr mv.src.val).1 + d.1).toNat + 48) = sq t'.file 6 := by
            apply Fin.ext
            show ((((fr mv.src.val).1 + d.1).toNat + 48) % 64 : Nat) = (6 * 8 + t'.file) % 64
            rw [hff, Nat.mod_eq_of_lt (by have := file_lt t'; omega),
              Nat.mod_eq_of_lt (by have := file_lt t'; omega)]
            omega
          have hK32 : c.isK (((fr mv.src.val).1 + d.1).toNat + 32) = false :=
            not_isK_of_board hf _ ⟨.black, .pawn⟩ (by rw [hsq4]; exact hbp4) (by decide) (by decide)
          have hK40 : c.isK (((fr mv.src.val).1 + d.1).toNat + 40) = false :=
            not_isK_of_none hf _ (by rw [hsq5]; exact hbn2)
          have hK48 : c.isK (((fr mv.src.val).1 + d.1).toNat + 48) = false :=
            not_isK_of_none hf _ (by rw [hsq6]; exact hb6)
          have his : (r.ep.lookup (((fr mv.src.val).1 + d.1).toNat)).isSome = true := by
            rw [hr.2.1 _ hf8, hK32, hK40, hK48]
            rfl
          cases hlo : r.ep.lookup (((fr mv.src.val).1 + d.1).toNat) with
          | none => rw [hlo] at his; simp at his
          | some v =>
            obtain ⟨-, hv0, hvd⟩ := hr.1 _ v (mem_of_lookup hlo)
            obtain ⟨hi, hd2⟩ := Array.getElem?_eq_some_iff.mp hvd
            have hvE : (Ex.v v).eval A = true := by
              show litVal A v = true
              rw [show litVal A v = A v.toNat from by
                show (if 0 < v then A v.toNat else !A v.natAbs) = A v.toNat
                rw [if_pos hv0]]
              have hG := hg _ hi
              rw [hd2, show v.toNat - 1 + 1 = v.toNat from by omega] at hG
              rw [hG]
              show (p.ep == some (toSq (((fr mv.src.val).1 + d.1).toNat + 40))) = true
              rw [beq_iff_eq, hepmv, hsq5]
            have hKt' : c.isK t'.val = false := not_isK_of_none hf _ (by rw [toSq_val t']; exact hbn2)
            have hpsv : (Ex.and [c.p mv.src.val 0, .v v]).eval A = true := by
              rw [eval_and2, Bool.and_eq_true]
              exact ⟨heP, hvE⟩
            have hmvl : (c.mkMove mv.src.val t'.val none 0 (.and [c.p mv.src.val 0, .v v]) (sqo ((fr mv.src.val).1 + d.1) 4) 1).mv ∈ legalMoves p := by
              show (⟨toSq mv.src.val, toSq t'.val, (none : Option Nat).map kindOf⟩ : Move) ∈ legalMoves p
              rw [Option.map_none, toSq_val mv.src, toSq_val t', ← hmk]
              exact h
            have hcov : mv ∈ (c.mkMove mv.src.val t'.val none 0 (.and [c.p mv.src.val 0, .v v]) (sqo ((fr mv.src.val).1 + d.1) 4) 1).covers := by
              rw [hmk]
              exact covers_single_mem _ _ _ _ mv.src t' (toSq_val mv.src) (toSq_val t')
            exact complete_pawn_aux hf hg hl hr mv h hps hk t'.val
              (.and [c.p mv.src.val 0, .v v]) (sqo ((fr mv.src.val).1 + d.1) 4) 1 none t'.isLt
              (mem_pawnCands_ep hrk hdf hsqo hKt' hr4 v hlo) hpsv hmvl hcov
      · have hbnu : p.board u = none := board_none_of_empty he1
        have hbn : p.board t' = none := board_none_of_empty he2
        have hsqo1 : sqo (fr mv.src.val).1 ((fr mv.src.val).2 + 1) = some u.val := by
          have e := (off_sqo_some mv.src u 0 1).mp hof1
          rwa [Int.add_zero] at e
        have hsqo2 : sqo (fr mv.src.val).1 ((fr mv.src.val).2 + 2) = some t'.val := by
          have e := (off_sqo_some mv.src t' 0 2).mp hof2
          rwa [Int.add_zero] at e
        have hsr1 : (fr mv.src.val).2 = 1 := by
          rw [fr2_rank mv.src, hsr]
          rfl
        have hsqo3 : sqo (fr mv.src.val).1 3 = some t'.val := by
          have e := hsqo2
          rwa [hsr1] at e
        have hKt' : c.isK t'.val = false := not_isK_of_none hf _ (by rw [toSq_val t']; exact hbn)
        have hKtu : c.isK u.val = false := not_isK_of_none hf _ (by rw [toSq_val u]; exact hbnu)
        have h7f : ((fr t'.val).2 == 7) = false := by
          rw [beq_eq_false_iff_ne, sqo_snd hsqo3]
          decide
        have hpsv : (Ex.and [c.p mv.src.val 0, c.empty u.val, c.empty t'.val]).eval A = true := by
          have hb2' : (c.empty u.val).eval A = true := by
            rw [eval_empty hf hg hl _ u.isLt, toSq_val u, hbnu, Option.isNone_none]
          have hb3' : (c.empty t'.val).eval A = true := by
            rw [eval_empty hf hg hl _ t'.isLt, toSq_val t', hbn, Option.isNone_none]
          rw [eval_and3, Bool.and_eq_true]
          exact ⟨heP, by rw [Bool.and_eq_true]; exact ⟨hb2', hb3'⟩⟩
        have hmvl : (c.mkMove mv.src.val t'.val none 0 (.and [c.p mv.src.val 0, c.empty u.val, c.empty t'.val]) none 1).mv ∈ legalMoves p := by
          show (⟨toSq mv.src.val, toSq t'.val, (none : Option Nat).map kindOf⟩ : Move) ∈ legalMoves p
          rw [Option.map_none, toSq_val mv.src, toSq_val t', ← hm]
          exact h
        have hcov : mv ∈ (c.mkMove mv.src.val t'.val none 0 (.and [c.p mv.src.val 0, c.empty u.val, c.empty t'.val]) none 1).covers := by
          rw [hm]
          exact covers_single_mem _ _ _ _ mv.src t' (toSq_val mv.src) (toSq_val t')
        exact complete_pawn_aux hf hg hl hr mv h hps hk t'.val
          (.and [c.p mv.src.val 0, c.empty u.val, c.empty t'.val]) none 1 none t'.isLt
          (mem_pawnCands_push2 hrk hsqo1 hKtu hsqo3 hKt' hsr1 (mem_mkPawn_single _ h7f)) hpsv hmvl hcov
    · exact absurd rfl hknp
  · obtain ⟨hsrc, -, hb2, -, -⟩ := castleMoves_cases hcm
    rw [hsrc, hb2] at hk
    have e9 := Option.some.inj hk
    simp only [Piece.mk.injEq] at e9
    exact absurd e9.2 (by decide)


def Cfg.kingCand (c : Cfg) (t : Nat) : Cand :=
  { src := c.kw, dst := t, promo := none, T := 5, ep := none,
    pseudo := Ex.not (c.wocc t), w := 1, skip := false,
    legal := .and [Ex.not (c.wocc t), .not (c.attB t [c.kw] [] [t])],
    chk := c.attW c.kb [c.kw] [t] [t] t }

theorem kingCand_mv (t : Nat) : (c.kingCand t).mv = ⟨toSq c.kw, toSq t, none⟩ := rfl

theorem kingCand_mem (t : Nat) (ht : t < 64)
    (hcond : (cheb c.kw t == 1 && (1 < cheb c.kb t)) = true) :
    c.kingCand t ∈ c.kingCands := by
  show _ ∈ (List.range 64).filterMap fun t' =>
    if (cheb c.kw t' == 1 && decide (1 < cheb c.kb t')) = true then some (c.kingCand t') else none
  exact List.mem_filterMap.mpr ⟨t, List.mem_range.mpr ht, by rw [if_pos hcond]⟩

theorem complete_king (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hr : RightsOk c s r)
    (mv : Move) (h : mv ∈ legalMoves p) (hk : p.board mv.src = some ⟨.white, .king⟩) :
    ∃ m ∈ c.cands r, m.legal.eval A = true ∧ mv ∈ m.covers := by
  have hturn : p.turn = .white := hf.2.1
  have hA := hf.1
  have hps : mv ∈ pseudo p := (mem_legalMoves h).1
  obtain ⟨hwk, hbkk, -⟩ := fits_kings hf
  obtain ⟨hbu, hbuniq⟩ := kingSq_spec p .black (hA.kings .black)
  have hksq : mv.src = kingSq p .white := (kingSq_spec p .white (hA.kings .white)).2 mv.src hk
  have hckw : c.kw = mv.src.val := by
    have hc := hf.2.2
    have e : c.kw = (kingSq p .white).val := by
      rw [← hc]
      rfl
    rw [e, hksq]
  have hckb : c.kb = (kingSq p .black).val := by
    have hc := hf.2.2
    rw [← hc]
    rfl
  have hkb64 : c.kb < 64 := hckb ▸ Fin.is_lt _
  by_cases hcast : isCastle p mv = true
  · have hcm : mv ∈ castleMoves p := by
      rcases pseudo_cases hps with ⟨s', q', hbs, hcol2, hpm⟩ | hcm
      · exfalso
        have hsrc : mv.src = s' := move_src_of_pieceMoves hpm
        subst hsrc
        rw [hk] at hbs
        obtain rfl := (Option.some.inj hbs).symm
        rcases pieceMoves_cases hpm with ⟨hkpp, -⟩ | ⟨-, -, hpn2, hdst⟩
        · exact absurd hkpp (by decide)
        · have hatt := (List.mem_filter.mp hdst).1
          rw [mem_attacks_king p.board mv.src mv.dst .white] at hatt
          have hd1 : dist mv.src mv.dst = 1 := by
            rw [← hatt, cheb_toSq mv.src.val mv.dst.val mv.src.isLt mv.dst.isLt, toSq_val mv.src,
              toSq_val mv.dst]
          unfold isCastle at hcast
          rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hcast
          unfold dist at hd1
          rcases hcast.2 with h2 | h2 <;> omega
      · exact hcm
    obtain ⟨hsrc2, hpn2, hbK2, hs4, hside2⟩ := castleMoves_cases hcm
    have hchk : c.chk = false := by
      have hc := hf.2.2
      have e : c.chk = inCheck p .white := by
        rw [← hc]
        rfl
      rw [e, inCheck_iff_attacked p .white (hA.kings .white),
        show kingSq p .white = sq 4 p.turn.home from hksq.symm.trans hsrc2, hturn]
      rw [hturn] at hs4
      exact hs4
    have hkwe : (c.kw == E1) = true := by
      rw [beq_iff_eq, hckw, hsrc2, hturn]
      show ((sq 4 Color.white.home).val : Nat) = 4
      rw [show Color.white.home = 0 from rfl]
      show (0 * 8 + 4) % 64 = 4
      rfl
    rcases hside2 with ⟨hdst, hck, hr7, h5, h6⟩ | ⟨hdst, hcq, hr0, h1e, h2e, h3e⟩
    · have hcorner : ((if true then H1 else A1) != c.kb) = true := by
        show ((7 : Nat) != c.kb) = true
        rw [bne_iff_ne]
        intro e
        rw [← e] at hbkk
        rw [show toSq (7 : Nat) = sq 7 Color.white.home from by
          apply Fin.ext
          show 7 % 64 = (Color.white.home * 8 + 7) % 64
          rfl] at hbkk
        rw [hturn] at hr7
        rw [hbkk] at hr7
        have e9 := Option.some.inj hr7
        simp only [Piece.mk.injEq] at e9
        exact absurd e9.1 (by decide)
      have his : (r.cr.lookup true).isSome = true := by
        rw [hr.2.2.2 true, hkwe, hchk, hcorner]
        rfl
      cases hlk : r.cr.lookup true with
      | none => rw [hlk] at his; simp at his
      | some v =>
        have hmem2 : c.castleK v ∈ c.castleCands r := by
          show _ ∈ (r.cr.lookup true).toList.map c.castleK ++ (r.cr.lookup false).toList.map c.castleQ
          rw [hlk, Option.toList_some]
          exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨v, List.mem_singleton_self v, rfl⟩))
        have hcamv : (c.castleK v).mv = mv := by
          rw [show mv = ⟨sq 4 p.turn.home, sq 6 p.turn.home, none⟩ from by
            rw [show mv = ⟨mv.src, mv.dst, mv.promo⟩ from rfl]
            rw [hsrc2, hdst, hpn2]]
          rw [hturn]
          show (⟨toSq E1, toSq G1, (none : Option Nat).map kindOf⟩ : Move) =
            ⟨sq 4 Color.white.home, sq 6 Color.white.home, none⟩
          rw [show toSq E1 = sq 4 Color.white.home from by
            apply Fin.ext
            show E1 % 64 = (Color.white.home * 8 + 4) % 64
            rfl, show toSq G1 = sq 6 Color.white.home from by
            apply Fin.ext
            show G1 % 64 = (Color.white.home * 8 + 6) % 64
            rfl, Option.map_none]
        have hleg : (c.castleK v).legal.eval A = true := by
          rw [castle_legal hf hg hl hr _ hmem2, hcamv]
          exact decide_eq_true h
        have hcov : mv ∈ (c.castleK v).covers := by
          rw [show (c.castleK v).covers = [(c.castleK v).mv] from by
            simp [Cand.covers, show (c.castleK v).w = 1 from rfl]]
          exact List.mem_singleton.mpr hcamv.symm
        exact ⟨_, (mem_cands _).mpr (Or.inr (Or.inr hmem2)), hleg, hcov⟩
    · have hcorner : ((if false then H1 else A1) != c.kb) = true := by
        show ((0 : Nat) != c.kb) = true
        rw [bne_iff_ne]
        intro e
        have e2 : c.kb = 0 := e.symm
        rw [e2] at hbkk
        rw [show toSq (0 : Nat) = sq 0 Color.white.home from by
          apply Fin.ext
          show 0 % 64 = (Color.white.home * 8 + 0) % 64
          rfl] at hbkk
        rw [hturn] at hr0
        rw [hbkk] at hr0
        have e9 := Option.some.inj hr0
        simp only [Piece.mk.injEq] at e9
        exact absurd e9.1 (by decide)
      have his : (r.cr.lookup false).isSome = true := by
        rw [hr.2.2.2 false, hkwe, hchk, hcorner]
        rfl
      cases hlk : r.cr.lookup false with
      | none => rw [hlk] at his; simp at his
      | some v =>
        have hmem2 : c.castleQ v ∈ c.castleCands r := by
          show _ ∈ (r.cr.lookup true).toList.map c.castleK ++ (r.cr.lookup false).toList.map c.castleQ
          rw [hlk, Option.toList_some]
          exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨v, List.mem_singleton_self v, rfl⟩))
        have hcamv : (c.castleQ v).mv = mv := by
          rw [show mv = ⟨sq 4 p.turn.home, sq 2 p.turn.home, none⟩ from by
            rw [show mv = ⟨mv.src, mv.dst, mv.promo⟩ from rfl]
            rw [hsrc2, hdst, hpn2]]
          rw [hturn]
          show (⟨toSq E1, toSq C1, (none : Option Nat).map kindOf⟩ : Move) =
            ⟨sq 4 Color.white.home, sq 2 Color.white.home, none⟩
          rw [show toSq E1 = sq 4 Color.white.home from by
            apply Fin.ext
            show E1 % 64 = (Color.white.home * 8 + 4) % 64
            rfl, show toSq C1 = sq 2 Color.white.home from by
            apply Fin.ext
            show C1 % 64 = (Color.white.home * 8 + 2) % 64
            rfl, Option.map_none]
        have hleg : (c.castleQ v).legal.eval A = true := by
          rw [castle_legal hf hg hl hr _ hmem2, hcamv]
          exact decide_eq_true h
        have hcov : mv ∈ (c.castleQ v).covers := by
          rw [show (c.castleQ v).covers = [(c.castleQ v).mv] from by
            simp [Cand.covers, show (c.castleQ v).w = 1 from rfl]]
          exact List.mem_singleton.mpr hcamv.symm
        exact ⟨_, (mem_cands _).mpr (Or.inr (Or.inr hmem2)), hleg, hcov⟩
  · have hcf : isCastle p mv = false := by
      cases h2 : isCastle p mv with
      | false => rfl
      | true => exact absurd h2 hcast
    have hepf : isEp p mv = false := by
      unfold isEp
      have e : (p.board mv.src).any (fun x => x.kind == .pawn) = false :=
        any_kind_ne p.board mv.src .king .pawn (by rw [hk]; rfl) (by decide)
      rw [e]
      rfl
    rcases pseudo_cases hps with ⟨s', q', hbs, hcol2, hpm⟩ | hcm
    · have hsrc : mv.src = s' := move_src_of_pieceMoves hpm
      subst hsrc
      rw [hk] at hbs
      obtain rfl := (Option.some.inj hbs).symm
      rcases pieceMoves_cases hpm with ⟨hkpp, -⟩ | ⟨-, -, hpn, hdst⟩
      · exact absurd hkpp (by decide)
      · have hatt := (List.mem_filter.mp hdst).1
        rw [mem_attacks_king p.board mv.src mv.dst .white] at hatt
        have hcheb1 : (cheb c.kw mv.dst.val == 1) = true := beq_iff_eq.mpr (by
          rw [hckw]
          exact hatt)
        have hA2 : Admissible (play p mv) := admissible_play hA h
        have hb1 : (play p mv).board mv.dst = some ⟨.white, .king⟩ := by
          rw [play_board_simple p mv hcf hepf mv.dst, if_pos rfl]
          show moved p mv = some ⟨.white, .king⟩
          rw [moved, hpn]
          exact hk
        have hwd : mv.dst ≠ kingSq p .black := by
          intro e
          have hnk := pseudo_no_king_capture hA hps
          rw [hturn] at hnk
          rw [← e] at hbu
          exact hnk hbu
        have hws : mv.src ≠ kingSq p .black := by
          intro e
          rw [e] at hk
          rw [hbu] at hk
          have e9 := Option.some.inj hk
          simp only [Piece.mk.injEq] at e9
          exact absurd e9.1 (by decide)
        have hb2 : (play p mv).board (kingSq p .black) = some ⟨.black, .king⟩ := by
          rw [play_board_simple p mv hcf hepf (kingSq p .black), if_neg (fun e => hwd e.symm),
            if_neg (fun e => hws e.symm)]
          exact hbu
        obtain ⟨hw2, huw2⟩ := kingSq_spec (play p mv) .white (play_kings hA h .white)
        obtain ⟨hb2k, hub2⟩ := kingSq_spec (play p mv) .black (play_kings hA h .black)
        have hkw2 : kingSq (play p mv) .white = mv.dst := (huw2 mv.dst hb1).symm
        have hkb2 : kingSq (play p mv) .black = kingSq p .black := (hub2 (kingSq p .black) hb2).symm
        have hapart : 1 < dist (kingSq p .black) mv.dst := by
          have hap := hA2.apart
          rw [hkw2, hkb2] at hap
          rw [dist_comm mv.dst (kingSq p .black)] at hap
          exact hap
        have hcheb2 : decide (1 < cheb c.kb mv.dst.val) = true := by
          rw [decide_eq_true_iff]
          rw [cheb_toSq c.kb mv.dst.val hkb64 mv.dst.isLt, hckb, toSq_val (kingSq p .black),
            toSq_val mv.dst]
          exact hapart
        have hcond : (cheb c.kw mv.dst.val == 1 && (1 < cheb c.kb mv.dst.val)) = true := by
          rw [Bool.and_eq_true]
          exact ⟨hcheb1, hcheb2⟩
        have hmem2 : c.kingCand mv.dst.val ∈ c.kingCands := kingCand_mem _ mv.dst.isLt hcond
        have hcamv : (c.kingCand mv.dst.val).mv = mv := by
          rw [kingCand_mv, show toSq c.kw = mv.src from by rw [hckw, toSq_val mv.src],
            toSq_val mv.dst, ← hpn]
        have hleg : (c.kingCand mv.dst.val).legal.eval A = true := by
          rw [king_legal hf hg hl _ hmem2, hcamv]
          exact decide_eq_true h
        have hcov : mv ∈ (c.kingCand mv.dst.val).covers := by
          rw [show (c.kingCand mv.dst.val).covers = [(c.kingCand mv.dst.val).mv] from by
            simp [Cand.covers, show (c.kingCand mv.dst.val).w = 1 from rfl]]
          exact List.mem_singleton.mpr hcamv.symm
        exact ⟨_, (mem_cands _).mpr (Or.inr (Or.inl hmem2)), hleg, hcov⟩
    · obtain ⟨hsrc2, hpn2, hbK2, hs4, hside2⟩ := castleMoves_cases hcm
      have hcast2 : isCastle p mv = true := by
        unfold isCastle
        rw [Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · rw [hsrc2, hbK2]
          rfl
        · rcases hside2 with ⟨hdst, -⟩ | ⟨hdst, -⟩
          · rw [Bool.or_eq_true, beq_iff_eq]
            refine Or.inl ?_
            rw [hsrc2, hdst, hturn]
            show (sq 4 Color.white.home).file + 2 = (sq 6 Color.white.home).file
            rw [show Color.white.home = 0 from rfl, sq_file 4 0 (by decide) (by decide),
              sq_file 6 0 (by decide) (by decide)]
          · rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
            refine Or.inr ?_
            rw [hsrc2, hdst, hturn]
            show (sq 2 Color.white.home).file + 2 = (sq 4 Color.white.home).file
            rw [show Color.white.home = 0 from rfl, sq_file 2 0 (by decide) (by decide),
              sq_file 4 0 (by decide) (by decide)]
      exact absurd hcast2 (by rw [hcf]; exact Bool.false_ne_true)

theorem cand_complete (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hr : RightsOk c s r)
    (mv : Move) (h : mv ∈ legalMoves p) : ∃ m ∈ c.cands r, m.legal.eval A = true ∧ mv ∈ m.covers := by
  obtain ⟨⟨col, k⟩, hq, hc⟩ := pseudo_src (mem_legalMoves h).1
  have hw : col = .white := by simpa [hf.2.1] using hc
  subst hw
  cases k with
  | pawn => exact complete_pawn hf hg hl hr mv h hq
  | king => exact complete_king hf hg hl hr mv h hq
  | knight => exact complete_piece hf hg hl mv h ⟨_, hq, by decide, by decide⟩
  | bishop => exact complete_piece hf hg hl mv h ⟨_, hq, by decide, by decide⟩
  | rook => exact complete_piece hf hg hl mv h ⟨_, hq, by decide, by decide⟩
  | queen => exact complete_piece hf hg hl mv h ⟨_, hq, by decide, by decide⟩

theorem cand_w (m : Cand) (hm : m ∈ c.cands r) : m.w = 0 ∨ m.w = 1 ∨ m.w = 4 := by
  rcases (mem_cands m).mp hm with ⟨q, hq, hm⟩ | hm | hm
  · rcases hm with hm | hm
    · obtain ⟨-, -, -, -, -, -, -, hw⟩ := pieceCands_mk q hq m hm
      exact Or.inr (Or.inl hw)
    · obtain ⟨-, -, -, -, -, -, hw⟩ := pawnCands_mk q hq m hm
      rw [hw]
      split
      · exact Or.inr (Or.inl rfl)
      · split
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
  · simp only [Cfg.kingCands, List.mem_filterMap] at hm
    obtain ⟨t, -, htm⟩ := hm
    split at htm
    · simp only [Option.some.injEq] at htm
      subst htm
      exact Or.inr (Or.inl rfl)
    · simp at htm
  · simp only [Cfg.castleCands, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ <;> exact Or.inr (Or.inl rfl)

theorem covers_length (m : Cand) (hw : m.w = 0 ∨ m.w = 1 ∨ m.w = 4) : m.covers.length = m.w := by
  rcases hw with h | h | h <;> simp [Cand.covers, h]

theorem count_le (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hr : RightsOk c s r) :
    (legalMoves p).length ≤ (((c.cands r).filter (·.legal.eval A)).map (·.w)).sum := by
  have hsub : ∀ mv ∈ legalMoves p,
      mv ∈ ((c.cands r).filter fun m => m.legal.eval A).flatMap Cand.covers := by
    intro mv hmv
    obtain ⟨m, hmc, hml, hcv⟩ := cand_complete hf hg hl hr mv hmv
    exact List.mem_flatMap.mpr ⟨m, List.mem_filter.mpr ⟨hmc, hml⟩, hcv⟩
  have h1 : (legalMoves p).length ≤
      (((c.cands r).filter fun m => m.legal.eval A).flatMap Cand.covers).length :=
    (legalMoves_nodup p).length_le_of_subset hsub
  rw [List.length_flatMap] at h1
  rw [show (((c.cands r).filter fun m => m.legal.eval A).map fun m => m.covers.length) =
      (((c.cands r).filter fun m => m.legal.eval A).map fun m => m.w) from
    map_congr_mem _ (fun m hm => covers_length m (cand_w m (List.mem_filter.mp hm).1))] at h1
  exact h1

end Cands

section E3H

variable {c : Cfg} {s : St} {r : Rights}

theorem e3_boundedAll_map {n : Nat} {f : Nat → Ex} {ks : List Nat} (h : ∀ k ∈ ks, (f k).Bounded n) :
    Ex.BoundedAll n (ks.map f) := by
  induction ks with
  | nil => trivial
  | cons j ks ih => exact ⟨h j List.mem_cons_self, ih fun k hk => h k (List.mem_cons_of_mem j hk)⟩

theorem e3_boundedAll_append {n : Nat} {es₁ es₂ : List Ex} (h₁ : Ex.BoundedAll n es₁)
    (h₂ : Ex.BoundedAll n es₂) : Ex.BoundedAll n (es₁ ++ es₂) := by
  induction es₁ with
  | nil => exact h₂
  | cons e es₁ ih => exact ⟨h₁.1, ih h₁.2⟩

theorem e3_boundedAll_flatMap {n : Nat} {α : Type} {f : α → List Ex} {L : List α}
    (h : ∀ d ∈ L, Ex.BoundedAll n (f d)) : Ex.BoundedAll n (L.flatMap f) := by
  induction L with
  | nil => trivial
  | cons d L ih =>
    exact e3_boundedAll_append (h d List.mem_cons_self) (ih fun d' hd' => h d' (List.mem_cons_of_mem d hd'))

theorem e3_boundedAll_filterMap {n : Nat} {α : Type} {f : α → Option Ex} {L : List α}
    (h : ∀ a ∈ L, ∀ e, f a = some e → e.Bounded n) : Ex.BoundedAll n (L.filterMap f) := by
  induction L with
  | nil => trivial
  | cons a L ih =>
    cases hfa : f a with
    | none =>
      rw [List.filterMap_cons_none hfa]
      exact ih fun a' ha' => h a' (List.mem_cons_of_mem a ha')
    | some e =>
      rw [List.filterMap_cons_some hfa]
      exact ⟨h a List.mem_cons_self e hfa, ih fun a' ha' => h a' (List.mem_cons_of_mem a ha')⟩

theorem e3_p_bounded (hs : Inv s) (hl : Layout c s) (q k : Nat) (hq : q < 64) (hk : k < 11) :
    (c.p q k).Bounded s.nv := by
  by_cases hK : c.isK q = true
  · rw [show c.p q k = .k false from by simp only [Cfg.p, if_pos hK]]
    trivial
  · have he : c.isK q = false := Bool.eq_false_of_ne_true hK
    rw [show c.p q k = .v (c.xv q k) from by simp only [Cfg.p, if_neg hK]]
    exact layout_bounded hs hl q k
      (List.mem_filter.mpr ⟨List.mem_range.mpr hq, by simp only [he, Bool.not_false]⟩) hk

theorem e3_has_bounded (hs : Inv s) (hl : Layout c s) (q : Nat) (hq : q < 64) (ks : List Nat)
    (hks : ∀ k ∈ ks, k < 11) : (c.has q ks).Bounded s.nv :=
  e3_boundedAll_map fun k hk => e3_p_bounded hs hl q k hq (hks k hk)

theorem e3_empty_bounded (hs : Inv s) (hl : Layout c s) (q : Nat) (hq : q < 64) :
    (c.empty q).Bounded s.nv := e3_p_bounded hs hl q 10 hq (by decide)

theorem e3_wocc_bounded (hs : Inv s) (hl : Layout c s) (q : Nat) (hq : q < 64) :
    (c.wocc q).Bounded s.nv := by
  show (if q == c.kw then Ex.k true else c.has q symW).Bounded s.nv
  split
  · trivial
  · exact e3_has_bounded hs hl q hq symW (by decide)

theorem e3_clear_bounded (hs : Inv s) (hl : Layout c s) (a b : Nat) (emp occ : List Nat) :
    (c.clear a b emp occ).Bounded s.nv := by
  show (if ((between a b).filter (· ∉ emp)).any (· ∈ occ) then Ex.k false
    else Ex.and (((between a b).filter (· ∉ emp)).map c.empty)).Bounded s.nv
  split
  · trivial
  · apply e3_boundedAll_map
    intro q hq
    exact e3_empty_bounded hs hl q (between_lt64 (List.mem_filter.mp hq).1)

theorem e3_direct_bounded (hs : Inv s) (hl : Layout c s) (t T : Nat) (emp occ : List Nat) :
    (c.direct t T emp occ).Bounded s.nv := by
  unfold Cfg.direct
  split
  · trivial
  · split
    · trivial
    · show (match direction t c.kb with
        | none => Ex.k false
        | some d =>
          if (T == 3 && decide ¬(d ∈ orth) || T == 2 && decide ¬(d ∈ diag)) = true then Ex.k false
          else c.clear t c.kb emp occ).Bounded s.nv
      split
      · trivial
      · rename_i d hd
        split
        · trivial
        · show (c.clear t c.kb emp occ).Bounded s.nv
          exact e3_clear_bounded hs hl t c.kb emp occ

theorem e3_att_bounded (hs : Inv s) (hl : Layout c s) (K : Nat) (white : Bool) (k : Nat)
    (emp occ excl : List Nat) : (c.att K white k emp occ excl).Bounded s.nv := by
  show (Ex.or (((orth ++ diag).flatMap fun d =>
      (rayL K d).filterMap fun q =>
        if (decide (q ∈ emp) || decide (q ∈ occ) || decide (q ∈ excl)) = true then none
        else some (Ex.and [c.has q ((if d ∈ orth then [3, 4] else [2, 4]).map fun x => if white then x else x + 5),
          c.clear K q emp occ]))
    ++ ((knightL K).filterMap fun q =>
        if (decide (q ∈ emp) || decide (q ∈ occ) || decide (q ∈ excl)) = true then none
        else some (c.p q (if white then 1 else 6)))
    ++ ([(-1 : Int), 1].filterMap fun df =>
        match sqo ((fr K).1 + df) (if white then (fr K).2 - 1 else (fr K).2 + 1) with
        | some q =>
          if (decide (q ∈ emp) || decide (q ∈ occ) || decide (q ∈ excl)) = true then none
          else some (c.p q (if white then 0 else 5))
        | none => none)
    ++ (if (cheb k K == 1) = true then [Ex.k true] else []))).Bounded s.nv
  refine e3_boundedAll_append (e3_boundedAll_append (e3_boundedAll_append ?_ ?_) ?_) ?_
  · apply e3_boundedAll_flatMap
    intro d hd
    apply e3_boundedAll_filterMap
    intro q hq e he
    split at he
    · simp at he
    · obtain rfl := Option.some.inj he
      refine ⟨?_, ?_, trivial⟩
      · apply e3_has_bounded hs hl q (mem_rayL_lt hq)
        intro k hk
        simp only [List.mem_map] at hk
        obtain ⟨x, hx, rfl⟩ := hk
        by_cases hco : d ∈ orth
        · rw [if_pos hco] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · cases white <;> decide
          · rcases List.mem_cons.mp hx with rfl | hx
            · cases white <;> decide
            · exact absurd hx (List.not_mem_nil)
        · rw [if_neg hco] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · cases white <;> decide
          · rcases List.mem_cons.mp hx with rfl | hx
            · cases white <;> decide
            · exact absurd hx (List.not_mem_nil)
      · exact e3_clear_bounded hs hl K q emp occ
  · apply e3_boundedAll_filterMap
    intro q hq e he
    split at he
    · simp at he
    · obtain rfl := Option.some.inj he
      exact e3_p_bounded hs hl q _ (mem_knightL_lt hq) (by cases white <;> decide)
  · apply e3_boundedAll_filterMap
    intro df hdf e he
    split at he
    · rename_i q hsqo
      split at he
      · simp at he
      · obtain rfl := Option.some.inj he
        exact e3_p_bounded hs hl q _ (sqo_lt hsqo) (by cases white <;> decide)
    · simp at he
  · split
    · exact ⟨trivial, trivial⟩
    · trivial

theorem e3_attB_bounded (hs : Inv s) (hl : Layout c s) (K : Nat) (emp occ excl : List Nat) :
    (c.attB K emp occ excl).Bounded s.nv := e3_att_bounded hs hl K false c.kb emp occ excl

theorem e3_attW_bounded (hs : Inv s) (hl : Layout c s) (K : Nat) (emp occ excl : List Nat) (k : Nat) :
    (c.attW K emp occ excl k).Bounded s.nv := e3_att_bounded hs hl K true k emp occ excl

theorem e3_mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (a : α) (b : β)
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p t ih =>
    obtain ⟨k, b'⟩ := p
    rw [List.lookup_cons] at h
    split at h
    · next hkk =>
      rcases beq_iff_eq.mp hkk
      rcases Option.some.inj h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem e3_lit_bounded_of_def (hs : Inv s) (v : Int) (hv0 : 0 < v) {d : VDef}
    (h : s.defs[v.toNat - 1]? = some d) : (.v v : Ex).Bounded s.nv := by
  obtain ⟨hi, -⟩ := Array.getElem?_eq_some_iff.mp h
  have h1 := Int.natAbs_of_nonneg (Int.le_of_lt hv0)
  have h2 := Int.toNat_of_nonneg (Int.le_of_lt hv0)
  have hna : Int.natAbs v = Int.toNat v := Int.natCast_inj.mp (by rw [h1, h2])
  show 0 < (v : Int).natAbs ∧ (v : Int).natAbs ≤ s.nv
  rw [hna, hs.nv]
  have hp : 0 < v.toNat := Int.pos_iff_toNat_pos.mp hv0
  omega

theorem e3_mkMove_bounded (hs : Inv s) (hl : Layout c s) (q t : Nat) (pr : Option Nat) (T : Nat)
    (ps : Ex) (ep : Option Nat) (w : Nat) (hps : ps.Bounded s.nv) :
    (c.mkMove q t pr T ps ep w).pseudo.Bounded s.nv ∧
      (c.mkMove q t pr T ps ep w).legal.Bounded s.nv ∧
      (c.mkMove q t pr T ps ep w).chk.Bounded s.nv ∧
      ∀ A, (c.mkMove q t pr T ps ep w).skip = true → (c.mkMove q t pr T ps ep w).pseudo.eval A = false →
        (c.mkMove q t pr T ps ep w).legal.eval A = false := by
  have hm : c.mkMove q t pr T ps ep w =
      { src := q, dst := t, promo := pr, T := T, ep := ep, pseudo := ps, w := w, skip := true
        legal := .and [ps, .not (c.attB c.kw (q :: ep.toList) [t] [t])]
        chk := .or [c.direct t (pr.getD T) (q :: ep.toList) [], c.attW c.kb (q :: ep.toList) [t] [t]] } :=
    rfl
  rw [hm]
  refine ⟨hps, ⟨hps, e3_attB_bounded hs hl c.kw _ _ _, trivial⟩,
    ⟨e3_direct_bounded hs hl t (pr.getD T) _ _, e3_attW_bounded hs hl c.kb _ _ _ c.kw, trivial⟩, ?_⟩
  intro A _ hps'
  show (Ex.and [ps, Ex.not (c.attB c.kw (q :: ep.toList) [t] [t])]).eval A = false
  rw [show (Ex.and [ps, Ex.not (c.attB c.kw (q :: ep.toList) [t] [t])]).eval A =
      (ps.eval A && (Ex.not (c.attB c.kw (q :: ep.toList) [t] [t])).eval A) from by
    simp [Ex.eval, Ex.evalAll]]
  rw [hps']
  exact Bool.false_and _

theorem e3_mkPawn_shape (q t : Nat) (ps : Ex) (m : Cand) (hm : m ∈ c.mkPawn q t ps) :
    ∃ pr w, m = c.mkMove q t pr 0 ps none w := by
  simp only [Cfg.mkPawn] at hm
  split at hm
  · simp only [List.mem_map] at hm
    obtain ⟨⟨T, w⟩, hTw, rfl⟩ := hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hTw
    rcases hTw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨some 1, 4, rfl⟩
    · exact ⟨some 2, 0, rfl⟩
    · exact ⟨some 3, 0, rfl⟩
    · exact ⟨some 4, 0, rfl⟩
  · simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨none, 1, rfl⟩

theorem e3_pawnCands_lform (hs : Inv s) (hl : Layout c s) (hr : RightsOk c s r) (q : Nat)
    (hq : q ∈ c.squares) (m : Cand) (hm : m ∈ c.pawnCands r q) :
    ∃ t pr ep ps w, m = c.mkMove q t pr 0 ps ep w ∧ t < 64 ∧ ps.Bounded s.nv := by
  have hq64 : q < 64 := List.mem_range.mp (List.mem_filter.mp hq).1
  have hpq : (c.p q 0).Bounded s.nv := e3_p_bounded hs hl q 0 hq64 (by decide)
  simp only [Cfg.pawnCands] at hm
  split at hm
  · simp at hm
  · rw [List.mem_append] at hm
    rcases hm with hm | hm
    · split at hm
      · simp at hm
      · rw [List.mem_append] at hm
        rcases hm with hm | hm
        · obtain ⟨pr, w, rfl⟩ := e3_mkPawn_shape q _ _ _ hm
          exact ⟨_, pr, none, _, w, rfl, sqo_getD_lt _ _,
            ⟨hpq, e3_empty_bounded hs hl _ (sqo_getD_lt _ _), trivial⟩⟩
        · split at hm
          · obtain ⟨pr, w, rfl⟩ := e3_mkPawn_shape q _ _ _ hm
            exact ⟨_, pr, none, _, w, rfl, sqo_getD_lt _ _,
              ⟨hpq, ⟨e3_empty_bounded hs hl _ (sqo_getD_lt _ _),
                ⟨e3_empty_bounded hs hl _ (sqo_getD_lt _ _), trivial⟩⟩⟩⟩
          · simp at hm
    · rcases List.mem_flatMap.mp hm with ⟨df, hdf, hm⟩
      split at hm
      · simp at hm
      · rename_i t htsqo
        split at hm
        · simp at hm
        · rw [List.mem_append] at hm
          rcases hm with hm | hm
          · obtain ⟨pr, w, rfl⟩ := e3_mkPawn_shape q _ _ _ hm
            exact ⟨_, pr, none, _, w, rfl, sqo_lt htsqo,
              ⟨hpq, e3_has_bounded hs hl t (sqo_lt htsqo) symB (by decide), trivial⟩⟩
          · split at hm
            · rename_i v hv
              rw [List.mem_singleton] at hm
              subst hm
              split at hv
              · next h4 =>
                obtain ⟨-, hv0, hvd⟩ := hr.1 _ v (e3_mem_of_lookup r.ep _ v hv)
                exact ⟨_, none, _, _, 1, rfl, sqo_lt htsqo,
                  ⟨hpq, e3_lit_bounded_of_def hs v hv0 hvd, trivial⟩⟩
              · simp at hv
            · simp at hm

theorem e3_triple_listMapM {α β : Type} (l : List α) (f : α → M β) (s : St) (hs : Inv s)
    (B : β → Nat → Prop)
    (hB : ∀ b n n', n ≤ n' → B b n → B b n')
    (V0 : α → β → Prop)
    (V : α → β → Pos → Assignment → Prop)
    (hf : ∀ m ∈ l, ∀ s₁, Inv s₁ → Ext s s₁ →
      Triple (f m) s₁ [] fun b s' => B b s'.nv ∧ V0 m b ∧ ∀ p A, Good p A s' → V m b p A) :
    Triple (List.mapM f l) s [] fun bs s' =>
      bs.length = l.length ∧ (∀ b ∈ bs, B b s'.nv) ∧
      ∀ i (h1 : i < l.length), ∀ (h2 : i < bs.length),
        V0 l[i] bs[i] ∧ ∀ p A, Good p A s' → V l[i] bs[i] p A := by
  induction l generalizing s with
  | nil =>
    rw [List.mapM_nil]
    exact triple_pure _ s hs [] _ ⟨rfl, (fun b hb => (List.not_mem_nil hb).elim),
      fun i h1 => absurd h1 (Nat.not_lt_zero i)⟩
  | cons a l ih =>
    rw [List.mapM_cons]
    refine triple_bind (hf a List.mem_cons_self s hs (ext_refl s)) ?_
    intro b s₁ hinv₁ hext₁ hof₁ hQ₁
    obtain ⟨hBb, hV0b, hVb⟩ := hQ₁
    refine triple_bind (ih s₁ hinv₁
      (fun m hm s₂ hinv₂ hext₁₂ => hf m (List.mem_cons_of_mem a hm) s₂ hinv₂ (ext_trans hext₁ hext₁₂))) ?_
    intro bs s₂ hinv₂ hext₂ hof₂ hQ₂
    obtain ⟨hlen, hBall, hVz⟩ := hQ₂
    refine triple_pure _ s₂ hinv₂ [] _ ⟨?_, ?_, ?_⟩
    · rw [List.length_cons, List.length_cons, hlen]
    · intro b' hb'
      rw [List.mem_cons] at hb'
      rcases hb' with rfl | hb'
      · exact hB b' s₁.nv s₂.nv (by rw [hinv₁.nv, hinv₂.nv]; exact hext₂.defs_le) hBb
      · exact hBall b' hb'
    · intro i h1 h2
      cases i with
      | zero =>
        show V0 (a :: l)[0] (b :: bs)[0] ∧ _
        exact ⟨hV0b, fun p A hg => hVb p A (good_mono hext₂ hg)⟩
      | succ i =>
        show V0 (a :: l)[i + 1] (b :: bs)[i + 1] ∧ _
        exact hVz i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

theorem e3_filter_replicate_length (n : Nat) (w : Wire) (A : Assignment) :
    ((List.replicate n w).filter (·.eval A)).length = if w.eval A then n else 0 := by
  induction n with
  | zero => cases w.eval A <;> rfl
  | succ n ih =>
    rw [List.replicate_succ, List.filter_cons]
    cases hv : w.eval A <;> simp [hv, ih]

theorem e3_countPhase_cnt_len (L : List (Cand × Wire × Wire)) (A : Assignment) :
    (((L.filter fun x => !(x.2.1 == Wire.ff)).flatMap fun x => List.replicate x.1.w x.2.1).filter
        (·.eval A)).length =
      ((L.filter fun x => x.2.1.eval A).map (·.1.w)).sum := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    by_cases hff : (x.2.1 == Wire.ff) = true
    · have hxw : x.2.1 = Wire.ff := beq_iff_eq.mp hff
      have hev : x.2.1.eval A = false := by rw [hxw]; rfl
      rw [List.filter_cons_of_neg (by simp [hff]), List.filter_cons_of_neg (by simp [hev])]
      exact ih
    · have haff : (x.2.1 == Wire.ff) = false := Bool.eq_false_of_ne_true hff
      rw [List.filter_cons_of_pos (by simp [haff]), List.flatMap_cons, List.filter_append,
        List.length_append, e3_filter_replicate_length]
      by_cases hev : x.2.1.eval A = true
      · rw [List.filter_cons_of_pos (by simp [hev]), List.map_cons, List.sum_cons, if_pos hev, ih]
      · rw [List.filter_cons_of_neg (p := fun x => Wire.eval A x.2.1) (a := x) (show
            ¬ (fun x => Wire.eval A x.2.1) x from hev), if_neg hev, ih]
        exact Nat.zero_add _

theorem e3_countPhase_loop (ms : Array (Cand × Wire × Wire)) (s : St) (hs : Inv s) :
    Triple (forIn ms.toList ([] : List Wire)
      (fun x cnt =>
        if (x.2.1 == Wire.ff) = true then pure (ForInStep.yield cnt)
        else
          (if (true && (x.2.2 != Wire.tt)) = true then
            emitW .allcheck [x.2.1.neg, x.2.2] >>= fun _ =>
              pure (ForInStep.yield (cnt ++ List.replicate x.1.w x.2.1))
          else pure (ForInStep.yield (cnt ++ List.replicate x.1.w x.2.1)))))
      s [.allcheck]
      fun cnt s' =>
        cnt = ((ms.toList.filter fun x => !(x.2.1 == Wire.ff)).flatMap fun x => List.replicate x.1.w x.2.1) ∧
        ∀ fc ∈ NewCls s s', ∃ x ∈ ms.toList, x.2.1 ≠ Wire.ff ∧ x.2.2 ≠ Wire.tt ∧ fc.1 = Fam.allcheck ∧
          ∀ A, fc.2.sat A = (x.2.1.neg.eval A || x.2.2.eval A) := by
  refine triple_forIn ms.toList [] _ s [.allcheck]
    (fun pre cnt s' =>
      cnt = ((pre.filter fun x => !(x.2.1 == Wire.ff)).flatMap fun x => List.replicate x.1.w x.2.1) ∧
      ∀ fc ∈ NewCls s s', ∃ x ∈ pre, x.2.1 ≠ Wire.ff ∧ x.2.2 ≠ Wire.tt ∧ fc.1 = Fam.allcheck ∧
        ∀ A, fc.2.sat A = (x.2.1.neg.eval A || x.2.2.eval A))
    hs ⟨rfl, ?_⟩ ?_
  · intro fc hfc
    rw [newCls_self] at hfc
    exact (List.not_mem_nil hfc).elim
  · intro pre a rest cnt s' hl' hinv' hext' hof' hI
    obtain ⟨hcnt, hcls⟩ := hI
    show Triple (if (a.2.1 == Wire.ff) = true then pure (ForInStep.yield cnt)
      else (if (true && (a.2.2 != Wire.tt)) = true then
        emitW .allcheck [a.2.1.neg, a.2.2] >>= fun _ =>
          pure (ForInStep.yield (cnt ++ List.replicate a.1.w a.2.1))
      else pure (ForInStep.yield (cnt ++ List.replicate a.1.w a.2.1)))) s' [.allcheck] _
    split
    · next hiff =>
      refine triple_pure (ForInStep.yield cnt) s' hinv' [.allcheck] _ ⟨?_, ?_⟩
      · rw [hcnt]
        have h0 : [a].filter (fun x => !(x.2.1 == Wire.ff)) = [] := by simp [hiff]
        rw [List.filter_append, h0, List.append_nil]
      · intro fc hfc
        obtain ⟨x, hx, hx1, hx2, hfam, hsat⟩ := hcls fc hfc
        exact ⟨x, List.mem_append_left _ hx, hx1, hx2, hfam, hsat⟩
    · next hiff =>
      have haff : (a.2.1 == Wire.ff) = false := Bool.eq_false_of_ne_true hiff
      have hane : a.2.1 ≠ Wire.ff := fun h => by rw [h] at haff; simp at haff
      have hcnt' : (cnt ++ List.replicate a.1.w a.2.1) =
          ((pre ++ [a]).filter fun x => !(x.2.1 == Wire.ff)).flatMap fun x => List.replicate x.1.w x.2.1 := by
        have h0 : [a].filter (fun x => !(x.2.1 == Wire.ff)) = [a] := by simp [haff]
        rw [hcnt, List.filter_append, h0, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
      split
      · next hck =>
        have hckne : a.2.2 ≠ Wire.tt := bne_iff_ne.mp (Bool.and_eq_true_iff.mp hck).2
        refine triple_bind (emitW_spec s' hinv' .allcheck (by decide) [a.2.1.neg, a.2.2]) ?_
        intro u s₂ hinv₂ hext₂ _ hQe
        refine triple_pure (ForInStep.yield (cnt ++ List.replicate a.1.w a.2.1)) s₂ hinv₂ [.allcheck] _
          ⟨hcnt', ?_⟩
        intro fc hfc
        rw [newCls_trans hext' hext₂] at hfc
        rcases List.mem_append.mp hfc with h | h
        · obtain ⟨x, hx, hx1, hx2, hfam, hsat⟩ := hcls fc h
          exact ⟨x, List.mem_append_left _ hx, hx1, hx2, hfam, hsat⟩
        · obtain ⟨hfam, hsat⟩ := hQe fc h
          refine ⟨a, List.mem_append_right _ (List.mem_singleton_self a), hane, hckne, hfam, fun A => ?_⟩
          rw [hsat A]
          simp
      · next hck =>
        refine triple_pure (ForInStep.yield (cnt ++ List.replicate a.1.w a.2.1)) s' hinv' [.allcheck] _
          ⟨hcnt', ?_⟩
        intro fc hfc
        obtain ⟨x, hx, hx1, hx2, hfam, hsat⟩ := hcls fc hfc
        exact ⟨x, List.mem_append_left _ hx, hx1, hx2, hfam, hsat⟩

end E3H

section E1H

variable {c : Cfg} {p : Pos} {A : Assignment} {s : St}

theorem e1_kings (hf : Fits c p) :
    (∀ t : Sq, p.board t = some ⟨.white, .king⟩ ↔ t = toSq c.kw) ∧
    (∀ t : Sq, p.board t = some ⟨.black, .king⟩ ↔ t = toSq c.kb) := by
  obtain ⟨hkw64, hkb64, -⟩ := fits_cfgOk hf
  obtain ⟨hpwb, hpbb, -⟩ := fits_kings hf
  have hA := hf.1
  have hkw2 : toSq c.kw = kingSq p .white :=
    Fin.ext (by rw [toSq_val_of_lt c.kw hkw64]; exact (congrArg Cfg.kw hf.2.2).symm)
  have hkb2 : toSq c.kb = kingSq p .black :=
    Fin.ext (by rw [toSq_val_of_lt c.kb hkb64]; exact (congrArg Cfg.kb hf.2.2).symm)
  exact ⟨fun t => ⟨fun ht => ((kingSq_spec p .white (hA.kings .white)).2 t ht).trans hkw2.symm,
      fun ht => ht ▸ hpwb⟩,
    fun t => ⟨fun ht => ((kingSq_spec p .black (hA.kings .black)).2 t ht).trans hkb2.symm,
      fun ht => ht ▸ hpbb⟩⟩

theorem e1_att_board (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (K : Nat) (hK : K < 64)
    (white : Bool) (k : Nat) (hk64 : k < 64)
    (hk : ∀ t : Sq, p.board t = some ⟨colOf white, .king⟩ ↔ t = toSq k) (hkx : 1 < cheb k K) :
    (c.att K white k [] [] []).eval A = attacked p.board (toSq K) (colOf white) := by
  refine (eval_att hf hg hl K hK white k hk64 [] [] [] p.board
    ⟨fun _ _ _ _ _ => rfl, fun q hq => by simp at hq, fun q hq => by simp at hq⟩
    (fun q hq => by simp at hq) (fun q hq => by simp at hq) (fun q hq => by simp at hq)
    (fun q hq => by simp at hq) hk (fun h => absurd h (by omega)) (by simp) (by simp)).trans ?_
  rw [Bool.eq_iff_iff, attacked_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨t, -, pc, hpc, hcol, hatt⟩
    exact ⟨t, pc, hpc, hcol, hatt⟩
  · rintro ⟨t, pc, hpc, hcol, hatt⟩
    exact ⟨t, by simp, pc, hpc, hcol, hatt⟩

theorem e1_attW_start (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) :
    (c.attW c.kb [] [] []).eval A = false := by
  obtain ⟨hkw64, hkb64, hcheb⟩ := fits_cfgOk hf
  obtain ⟨hw, hb⟩ := e1_kings hf
  have h1 := e1_att_board hf hg hl c.kb hkb64 true c.kw hkw64 hw hcheb
  have h2 : inCheck p .black = attacked p.board (toSq c.kb) .white :=
    inCheck_eq_of_uniq ((hb _).mpr rfl) (fun t ht => (hb t).mp ht)
  have h3 : inCheck p .black = false := by
    have h := hf.1.safe
    rw [hf.2.1] at h
    exact h
  exact h1.trans (h2.symm.trans h3)

theorem e1_attB_start (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) :
    (c.attB c.kw [] [] []).eval A = c.chk := by
  obtain ⟨hkw64, hkb64, hcheb⟩ := fits_cfgOk hf
  obtain ⟨hw, hb⟩ := e1_kings hf
  have h1 := e1_att_board hf hg hl c.kw hkw64 false c.kb hkb64 hb (by rw [cheb_symm]; exact hcheb)
  have h2 : inCheck p .white = attacked p.board (toSq c.kw) .black :=
    inCheck_eq_of_uniq ((hw _).mpr rfl) (fun t ht => (hw t).mp ht)
  have h3 : inCheck p .white = c.chk := congrArg Cfg.chk hf.2.2
  show (c.att c.kw false c.kb [] [] []).eval A = c.chk
  rw [h1, ← h3, h2]
  rfl

theorem e1_widen {α : Type} {x : M α} {s : St} {Q : α → St → Prop} (fs : List Fam) (h : Triple x s [] Q) :
    Triple x s fs fun a s' => Q a s' ∧ OnlyFams [.gate] s s' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun fc hfc => ?_, h4, h3⟩
  exact List.mem_cons.mpr (.inl (List.mem_singleton.mp (h3 fc hfc)))

theorem e1_ngs_trans {s₁ s₂ s₃ : St} (e12 : Ext s₁ s₂) (e23 : Ext s₂ s₃)
    (h12 : NonGateSat A s₁ s₂) (h23 : NonGateSat A s₂ s₃) : NonGateSat A s₁ s₃ := by
  intro fc hfc hfam
  rw [newCls_trans e12 e23, List.mem_append] at hfc
  rcases hfc with h | h
  · exact h12 fc h hfam
  · exact h23 fc h hfam

theorem e1_ngs_gate {s s' : St} (h : OnlyFams [.gate] s s') : NonGateSat A s s' := by
  intro fc hfc hfam
  rcases List.mem_cons.mp (h fc hfc) with h1 | h1
  · exact absurd h1 hfam
  · exact (List.not_mem_nil h1).elim

theorem e1_ngs_req {s s' : St} {f : Fam} {w : Wire}
    (h : ∀ fc ∈ NewCls s s', fc.1 = f ∧ ∀ A, fc.2.sat A = w.eval A) (hw : w.eval A = true) :
    NonGateSat A s s' := fun fc hfc _ => ((h fc hfc).2 A).trans hw


theorem e1_good_def {s : St} (hg : Good p A s) {i : Nat} {d : VDef} (h : s.defs[i]? = some d) :
    A (i + 1) = d.val p A := by
  obtain ⟨hi, hd⟩ := Array.getElem?_eq_some_iff.mp h
  rw [hg i hi, hd]

theorem e1_sat2 (a b : Int) : Clause.sat A #[a, b] = (litVal A a || litVal A b) := by
  show (#[a, b].any (litVal A)) = _
  rw [List.any_toArray]
  simp

theorem e1_newVar (s : St) (hs : Inv s) (fs : List Fam) (d : VDef) (hd : ∀ b L, d = .gate b L → False) :
    Triple (newVar d) s fs fun v s' => v = s.nv + 1 ∧ s'.defs[s.nv]? = some d ∧ NewCls s s' = [] ∧
      s'.nv = s.nv + 1 := by
  have hnc : NewCls s { s with nv := s.nv + 1, defs := s.defs.push d } = [] := by
    simp [NewCls, ← Array.length_toList]
  refine ⟨a4_newVar_inv hs hd, a4_newVar_ext s d, fun fc hfc => ?_, rfl, ?_, hnc, rfl⟩
  · have h : fc ∈ NewCls s { s with nv := s.nv + 1, defs := s.defs.push d } := hfc
    rw [hnc] at h
    exact (List.not_mem_nil h).elim
  · show (s.defs.push d)[s.nv]? = some d
    rw [hs.nv]
    exact Array.getElem?_push_size

theorem e1_mem_squares {q : Nat} (hq : q < 64) (h1 : q ≠ c.kw) (h2 : q ≠ c.kb) : q ∈ c.squares :=
  List.mem_filter.mpr ⟨List.mem_range.mpr hq, by simp [Cfg.isK, h1, h2]⟩

theorem e1_lit_xv (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (q k : Nat)
    (hq : q ∈ c.squares) (hk : k < 11) :
    (Wire.lit (c.xv q k)).eval A = (symOf (p.board (toSq q)) == k) := by
  obtain ⟨hpos, hd⟩ := hl q hq k hk
  obtain ⟨hi, hd2⟩ := Array.getElem?_eq_some_iff.mp hd
  have hA := hg _ hi
  rw [hd2] at hA
  show (if 0 < c.xv q k then A (c.xv q k).toNat else !A (c.xv q k).natAbs) =
    (symOf (p.board (toSq q)) == k)
  rw [if_pos hpos]
  have ht : (c.xv q k).toNat = 1 + 11 * c.xIdx q + k := Int.toNat_natCast _
  have e : (c.xv q k).toNat - 1 + 1 = (c.xv q k).toNat := by omega
  rw [← e]
  exact hA

theorem e1_cr_sat (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (hkw : c.kw = E1) (ks : Bool) (rq : Nat)
    (hrq : rq = if ks then H1 else A1) (hkb : rq ≠ c.kb) (n : Nat) (hd : s.defs[n]? = some (.cr ks)) :
    Clause.sat A #[-((n + 1 : Nat) : Int), c.xv rq 3] = true := by
  rw [e1_sat2, litValNeg (by omega), litValNat (by omega), e1_good_def hg hd]
  have hmem : rq ∈ c.squares := by
    refine e1_mem_squares (by cases ks <;> (rw [hrq]; decide)) ?_ hkb
    rw [hkw]
    cases ks <;> (rw [hrq]; decide)
  have hx := e1_lit_xv hf hg hl rq 3 hmem (by decide)
  have hx2 : litVal A (c.xv rq 3) = (symOf (p.board (toSq rq)) == 3) := hx
  rw [hx2]
  cases ks
  · show (!(p.castleQ .white) || _) = true
    cases hk : p.castleQ .white
    · rfl
    · obtain ⟨-, hr⟩ := hf.1.castleQ .white hk
      rw [hrq]
      have e : toSq (if false = true then H1 else A1) = sq 0 Color.white.home := rfl
      rw [e, hr]
      rfl
  · show (!(p.castleK .white) || _) = true
    cases hk : p.castleK .white
    · rfl
    · obtain ⟨-, hr⟩ := hf.1.castleK .white hk
      rw [hrq]
      have e : toSq (if true = true then H1 else A1) = sq 7 Color.white.home := rfl
      rw [e, hr]
      rfl

theorem e1_emit (s : St) (hs : Inv s) (f : Fam) (hf : f ≠ .gate) (c : Clause) :
    Triple (emit f c) s [f] fun _ s' => NewCls s s' = [(f, c)] ∧ s'.nv = s.nv :=
  ⟨a4_emit_inv hs hf c, a4_emit_ext s f c, a4_emit_of s f c, a4_emit_newCls s f c, rfl⟩

theorem e1_cr_mem {s' : St} {d : VDef} (n : Nat) (hd : s'.defs[n]? = some d) :
    0 < ((n + 1 : Nat) : Int) ∧ s'.defs[((n + 1 : Nat) : Int).toNat - 1]? = some d :=
  ⟨by omega, by rw [Int.toNat_natCast, Nat.add_sub_cancel]; exact hd⟩


theorem e1_pairs (s : St) (hs : Inv s) (n : Nat) (f : Fam) (hf : f ≠ .gate) (g : Nat → Int) :
    Triple (forIn (List.range n) PUnit.unit fun i _ => do
        forIn (List.range' (i + 1) (n - 1 - i)) PUnit.unit fun j _ => do
          emit f #[-(g i), -(g j)]
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)) s [f]
      fun _ s' => s'.nv = s.nv ∧ ∀ fc ∈ NewCls s s', ∃ i j, i < j ∧ j < n ∧ fc = (f, #[-(g i), -(g j)]) := by
  refine triple_forIn _ _ _ s [f] (fun _ _ s' => s'.nv = s.nv ∧
      ∀ fc ∈ NewCls s s', ∃ i j, i < j ∧ j < n ∧ fc = (f, #[-(g i), -(g j)])) hs
    ⟨rfl, fun fc hfc => by rw [newCls_self] at hfc; exact (List.not_mem_nil hfc).elim⟩ ?_
  intro pre a rest _ s₁ hl₁ hi₁ he₁ _ hI₁
  obtain ⟨hv₁, hc₁⟩ := hI₁
  have ha : a < n := List.mem_range.mp (hl₁ ▸ List.mem_append_right pre List.mem_cons_self)
  refine triple_bind (triple_forIn _ _ _ s₁ [f] (fun _ _ s' => s'.nv = s₁.nv ∧
      ∀ fc ∈ NewCls s₁ s', ∃ j, a < j ∧ j < n ∧ fc = (f, #[-(g a), -(g j)])) hi₁
    ⟨rfl, fun fc hfc => by rw [newCls_self] at hfc; exact (List.not_mem_nil hfc).elim⟩ ?_) ?_
  · intro pre' b rest' _ s₂ hl₂ hi₂ he₂ _ hI₂
    obtain ⟨hv₂, hc₂⟩ := hI₂
    have hb := List.mem_range'_1.mp (hl₂ ▸ List.mem_append_right pre' List.mem_cons_self)
    refine triple_bind (e1_emit s₂ hi₂ f hf _) ?_
    intro _ s₃ hi₃ he₃ _ hq₃
    obtain ⟨hn₃, hv₃⟩ := hq₃
    refine triple_pure _ s₃ hi₃ _ _ ⟨hv₃.trans hv₂, fun fc hfc => ?_⟩
    rw [newCls_trans he₂ he₃, List.mem_append, hn₃, List.mem_singleton] at hfc
    rcases hfc with h | h
    · exact hc₂ fc h
    · exact ⟨b, by omega, by omega, h⟩
  · intro _ s₂ hi₂ he₂ _ hq₂
    obtain ⟨hv₂, hc₂⟩ := hq₂
    refine triple_pure _ s₂ hi₂ _ _ ⟨hv₂.trans hv₁, fun fc hfc => ?_⟩
    rw [newCls_trans he₁ he₂, List.mem_append] at hfc
    rcases hfc with h | h
    · exact hc₁ fc h
    · obtain ⟨j, h1, h2, h3⟩ := hc₂ fc h
      exact ⟨a, j, h1, h2, h3⟩

theorem e1_ep_facts (hf : Fits c p) {f : Nat} (hf8 : f < 8) (h : p.ep = some (toSq (f + 40))) :
    p.board (toSq (f + 32)) = some ⟨.black, .pawn⟩ ∧ p.board (toSq (f + 40)) = none ∧
      p.board (toSq (f + 48)) = none := by
  have he : EpOk p (toSq (f + 40)) := hf.1.ep _ h
  unfold EpOk at he
  rw [hf.2.1] at he
  obtain ⟨-, h1, h2, h3⟩ := he
  have e1 : sq (toSq (f + 40)).file 4 = toSq (f + 32) :=
    Fin.ext (by show (4 * 8 + (f + 40) % 64 % 8) % 64 = (f + 32) % 64; omega)
  have e3 : sq (toSq (f + 40)).file 6 = toSq (f + 48) :=
    Fin.ext (by show (6 * 8 + (f + 40) % 64 % 8) % 64 = (f + 48) % 64; omega)
  rw [e1] at h1
  rw [e3] at h3
  exact ⟨h1, h2, h3⟩

theorem e1_ep_clause (hg : Good p A s) (hl : Layout c s) (hf : Fits c p) {f q k n : Nat}
    (hq : q ∈ c.squares) (hk : k < 11)
    (himp : p.ep = some (toSq (f + 40)) → symOf (p.board (toSq q)) = k) (hd : s.defs[n]? = some (.ep f)) :
    Clause.sat A #[-((n + 1 : Nat) : Int), c.xv q k] = true := by
  rw [e1_sat2, litValNeg (by omega), litValNat (by omega), e1_good_def hg hd]
  have hx2 : litVal A (c.xv q k) = (symOf (p.board (toSq q)) == k) := e1_lit_xv hf hg hl q k hq hk
  rw [hx2]
  show (!(p.ep == some (toSq (f + 40))) || _) = true
  cases he : (p.ep == some (toSq (f + 40)))
  · rfl
  · rw [himp (beq_iff_eq.mp he)]
    simp

theorem e1_mem_sq {q : Nat} (hq : q < 64) (h : c.isK q = false) : q ∈ c.squares :=
  List.mem_filter.mpr ⟨List.mem_range.mpr hq, by simp [h]⟩

theorem e1_ngs_single {s s' : St} {f : Fam} {cl : Clause} (h : NewCls s s' = [(f, cl)]) (hs : cl.sat A = true) :
    NonGateSat A s s' := by
  intro fc hfc _
  rw [h, List.mem_singleton] at hfc
  rw [hfc]
  exact hs

theorem e1_ngs_nil {s s' : St} (h : NewCls s s' = []) : NonGateSat A s s' := by
  intro fc hfc _
  rw [h] at hfc
  exact (List.not_mem_nil hfc).elim

theorem e1_ep_val (hg : Good p A s) {v : Int} {f : Nat} (hv : 0 < v) (hd : s.defs[v.toNat - 1]? = some (.ep f)) :
    litVal A v = (p.ep == some (toSq (f + 40))) := by
  rw [litVal, if_pos hv]
  have h := e1_good_def hg hd
  rw [Nat.sub_add_cancel (by omega)] at h
  exact h

theorem e1_range_prefix {n a : Nat} {pre rest : List Nat} (h : List.range n = pre ++ a :: rest) :
    a = pre.length := by
  have h1 := congrArg (fun l => l[pre.length]?) h
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero] at h1
  have hlt : pre.length < n := by
    have := congrArg List.length h
    simp at this
    omega
  rw [List.getElem?_range hlt] at h1
  exact (Option.some.inj h1).symm

theorem e1_filter_prefix (P : Nat → Bool) : ∀ (n : Nat) {a : Nat} {pre rest : List Nat},
    (List.range n).filter P = pre ++ a :: rest → pre = (List.range a).filter P
  | 0, a, pre, rest, h => by
    have := congrArg List.length h
    simp at this
  | n + 1, a, pre, rest, h => by
    rw [List.range_succ, List.filter_append] at h
    cases hP : P n
    · rw [List.filter_cons_of_neg (by simp [hP]), List.filter_nil, List.append_nil] at h
      exact e1_filter_prefix P n h
    · rw [List.filter_cons_of_pos hP, List.filter_nil] at h
      rcases List.append_eq_append_iff.mp h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
      · cases as with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at h2
          obtain ⟨rfl, -⟩ := h2
          rw [h1, List.append_nil]
        | cons b bs =>
          simp only [List.cons_append, List.cons.injEq] at h2
          have := congrArg List.length h2.2
          simp at this
      · cases bs with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at h2
          obtain ⟨rfl, -⟩ := h2
          rw [h1, List.append_nil]
        | cons b bs =>
          simp only [List.cons_append, List.cons.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          exact e1_filter_prefix P n h1

theorem e1_count (hne : c.kw ≠ c.kb) :
    ∀ a, ((List.range a).filter fun q => !c.isK q).length = c.xIdx a
  | 0 => by simp [Cfg.xIdx]
  | a + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, e1_count hne a]
    unfold Cfg.xIdx Cfg.isK
    by_cases h1 : a = c.kw
    · subst h1
      have h2 : (c.kw == c.kb) = false := beq_false_of_ne hne
      simp [h2]
      repeat' split
      all_goals omega
    · by_cases h2 : a = c.kb
      · subst h2
        have h3 : (c.kb == c.kw) = false := beq_false_of_ne (Ne.symm hne)
        simp [h3]
        repeat' split
        all_goals omega
      · have h3 : (a == c.kw) = false := beq_false_of_ne h1
        have h4 : (a == c.kb) = false := beq_false_of_ne h2
        simp [h3, h4]
        repeat' split
        all_goals omega

theorem e1_emitIn (s : St) (hs : Inv s) {fs : List Fam} {f : Fam} (hf : f ≠ .gate) (hfs : f ∈ fs) (cl : Clause) :
    Triple (emit f cl) s fs fun _ s' => NewCls s s' = [(f, cl)] ∧ s'.nv = s.nv :=
  triple_mono (e1_emit s hs f hf cl) (fun g hg => by rw [List.mem_singleton.mp hg]; exact hfs) (fun _ _ _ _ h => h)

theorem e1_x_loop (q : Nat) (s : St) (hs : Inv s) (fs : List Fam) :
    Triple (forIn (List.range 11) (#[] : Array Int) fun k L => do
        let v ← newVar (VDef.x q k)
        pure (ForInStep.yield (L.push (v : Int)))) s fs
      fun L s' => L.toList = (List.range 11).map (fun k => ((s.nv + 1 + k : Nat) : Int)) ∧ s'.nv = s.nv + 11 ∧
        (∀ k < 11, s'.defs[s.nv + k]? = some (.x q k)) ∧ NewCls s s' = [] := by
  refine triple_forIn _ _ _ s fs (fun pre L s' => L.toList = pre.map (fun k => ((s.nv + 1 + k : Nat) : Int)) ∧
      s'.nv = s.nv + pre.length ∧ (∀ k ∈ pre, s'.defs[s.nv + k]? = some (.x q k)) ∧ NewCls s s' = []) hs
    ⟨rfl, rfl, fun k h => (List.not_mem_nil h).elim, newCls_self s⟩ ?_ |>
    fun h => triple_mono h (fun f hf => hf) (fun L s' _ _ hq =>
      ⟨hq.1, hq.2.1, fun k hk => hq.2.2.1 k (List.mem_range.mpr hk), hq.2.2.2⟩)
  intro pre a rest L s₁ hl₁ hi₁ he₁ _ hI₁
  obtain ⟨hL₁, hv₁, hd₁, hn₁⟩ := hI₁
  have ha := e1_range_prefix hl₁
  refine triple_bind (e1_newVar s₁ hi₁ fs (.x q a) (fun _ _ h => VDef.noConfusion h)) ?_
  intro v s₂ hi₂ he₂ _ hq₂
  obtain ⟨rfl, hd₂, hn₂, hv₂⟩ := hq₂
  refine triple_pure _ s₂ hi₂ _ _ ⟨?_, ?_, ?_, ?_⟩
  · have e : s₁.nv + 1 = s.nv + 1 + a := by omega
    rw [Array.toList_push, hL₁, List.map_append, List.map_singleton, e]
  · rw [hv₂, hv₁, List.length_append]
    rfl
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact defs_mono he₂ (hd₁ k hk)
    · rw [List.mem_singleton.mp hk]
      have e : s.nv + a = s₁.nv := by omega
      rw [e]
      exact hd₂
  · rw [newCls_trans he₁ he₂, hn₁, hn₂]
    rfl

theorem e1_getL {L : Array Int} {n k : Nat} (hL : L.toList = (List.range 11).map (fun k => ((n + 1 + k : Nat) : Int)))
    (hk : k < 11) : L[k]! = ((n + 1 + k : Nat) : Int) := by
  have hsz : k < L.size := by
    rw [← Array.length_toList, hL, List.length_map, List.length_range]
    exact hk
  have h1 : L[k]? = some ((n + 1 + k : Nat) : Int) := by
    rw [← Array.getElem?_toList, hL, List.getElem?_map, List.getElem?_range hk]
    rfl
  rw [getElem!_pos L k hsz]
  exact Option.some.inj ((Array.getElem?_eq_getElem hsz).symm.trans h1)

theorem e1_xval {s' : St} (hg : Good p A s') {n k q : Nat} (hd : s'.defs[n + k]? = some (.x q k)) :
    litVal A ((n + 1 + k : Nat) : Int) = (symOf (p.board (toSq q)) == k) := by
  rw [litValNat (by omega), show n + 1 + k = n + k + 1 by omega]
  exact e1_good_def hg hd

theorem e1_sat1 (a : Int) : Clause.sat A #[a] = litVal A a := by
  show (#[a].any (litVal A)) = _
  rw [List.any_toArray]
  simp

theorem e1_sym0 {o : Option Piece} (h : symOf o = 0) : o = some ⟨.white, .pawn⟩ := by
  match o with
  | none => exact absurd h (by decide)
  | some ⟨col, k⟩ => cases col <;> cases k <;> first | rfl | exact absurd h (by decide)

theorem e1_sym5 {o : Option Piece} (h : symOf o = 5) : o = some ⟨.black, .pawn⟩ := by
  match o with
  | none => exact absurd h (by decide)
  | some ⟨col, k⟩ => cases col <;> cases k <;> first | rfl | exact absurd h (by decide)

theorem e1_rank {q : Nat} (hq : q < 64) (h : ((fr q).2 == 0 || (fr q).2 == 7) = true) :
    (toSq q).rank = 0 ∨ (toSq q).rank = 7 := by
  simp only [fr, Bool.or_eq_true, beq_iff_eq] at h
  show (q % 64) / 8 = 0 ∨ (q % 64) / 8 = 7
  omega

theorem e1_sq_facts {q : Nat} (hq : q ∈ c.squares) : q < 64 ∧ q ≠ c.kw ∧ q ≠ c.kb := by
  obtain ⟨h1, h2⟩ := List.mem_filter.mp hq
  have h3 : c.isK q = false := by simpa using h2
  unfold Cfg.isK at h3
  rw [Bool.or_eq_false_iff] at h3
  exact ⟨List.mem_range.mp h1, fun e => by simp [e] at h3, fun e => by simp [e] at h3⟩

end E1H

section Phases

variable (c : Cfg)

theorem e1_cr_body (ks : Bool) (rq : Nat) (cr : List (Bool × Int)) (s : St) (hs : Inv s) :
    Triple (if (rq != c.kb) = true then (do
        let v ← newVar (VDef.cr ks)
        emit Fam.castle #[-(v : Int), c.xv rq 3]
        pure (ForInStep.yield (cr ++ [(ks, (v : Int))]))) else pure (ForInStep.yield cr)) s [.castle]
      fun r s' => r = .yield (if (rq != c.kb) = true then cr ++ [(ks, ((s.nv + 1 : Nat) : Int))] else cr) ∧
        ((rq != c.kb) = true → s'.defs[s.nv]? = some (.cr ks)) ∧
        s'.nv = (if (rq != c.kb) = true then s.nv + 1 else s.nv) ∧ ∀ fc ∈ NewCls s s', (rq != c.kb) = true ∧ fc = (.castle, #[-((s.nv + 1 : Nat) : Int), c.xv rq 3]) := by
  split
  · next hq =>
    refine triple_bind (e1_newVar s hs _ (.cr ks) (fun _ _ h => VDef.noConfusion h)) ?_
    intro v s₁ hi₁ he₁ ho₁ hq₁
    obtain ⟨rfl, hd₁, hn₁, hv₁⟩ := hq₁
    refine triple_bind (e1_emit s₁ hi₁ .castle (by decide) _) ?_
    intro _ s₂ hi₂ he₂ _ hq₂
    obtain ⟨hq₂, hv₂⟩ := hq₂
    refine triple_pure _ s₂ hi₂ _ _ ⟨rfl, fun _ => defs_mono he₂ hd₁, hv₂.trans hv₁, ?_⟩
    intro fc hfc
    rw [newCls_trans he₁ he₂, List.mem_append] at hfc
    rcases hfc with h | h
    · rw [hn₁] at h
      exact (List.not_mem_nil h).elim
    · rw [hq₂] at h
      exact ⟨hq, List.mem_singleton.mp h⟩
  · next hq =>
    refine triple_pure _ s hs _ _ ⟨rfl, fun h => absurd h hq, rfl, fun fc hfc => ?_⟩
    rw [newCls_self] at hfc
    exact (List.not_mem_nil hfc).elim

theorem e1_ep_loop (s : St) (hs : Inv s) (hl : Layout c s) :
    Triple (forIn (List.range 8) ([] : List (Nat × Int)) fun f ep =>
        if (c.isK (f + 32) || c.isK (f + 40) || c.isK (f + 48)) = true then pure (ForInStep.yield ep)
        else do
          let v ← newVar (VDef.ep f)
          emit Fam.ep #[-(v : Int), c.xv (f + 32) 5]
          emit Fam.ep #[-(v : Int), c.xv (f + 40) EMP]
          emit Fam.ep #[-(v : Int), c.xv (f + 48) EMP]
          pure (ForInStep.yield (ep ++ [(f, (v : Int))]))) s [.ep]
      fun ep s' => (∀ f v, (f, v) ∈ ep → f < 8 ∧ 0 < v ∧ s'.defs[v.toNat - 1]? = some (.ep f)) ∧
        (∀ f, (ep.lookup f).isSome = (decide (f ∈ List.range 8) &&
          !(c.isK (f + 32) || c.isK (f + 40) || c.isK (f + 48)))) ∧
        ep.Pairwise (fun x y => x.1 ≠ y.1) ∧
        ∀ p A, Fits c p → Good p A s' → NonGateSat A s s' := by
  refine triple_forIn _ _ _ s [.ep] (fun pre ep s' =>
      (∀ f v, (f, v) ∈ ep → f ∈ pre ∧ f < 8 ∧ 0 < v ∧ s'.defs[v.toNat - 1]? = some (.ep f)) ∧
      (∀ f, (ep.lookup f).isSome = (decide (f ∈ pre) &&
        !(c.isK (f + 32) || c.isK (f + 40) || c.isK (f + 48)))) ∧
      ep.Pairwise (fun x y => x.1 ≠ y.1) ∧
      ∀ p A, Fits c p → Good p A s' → NonGateSat A s s') hs ⟨fun f v h => (List.not_mem_nil h).elim,
      fun f => rfl, List.Pairwise.nil,
      fun p A _ _ fc hfc => by rw [newCls_self] at hfc; exact (List.not_mem_nil hfc).elim⟩ ?_ |>
    fun h => triple_mono h (fun f hf => hf) (fun ep s' _ _ hq =>
      ⟨fun f v hm => (hq.1 f v hm).2, hq.2.1, hq.2.2.1, hq.2.2.2⟩)
  intro pre a rest ep s₁ hl₁ hi₁ he₁ _ hI₁
  obtain ⟨hm₁, hk₁, hp₁, hn₁⟩ := hI₁
  have ha : a < 8 := List.mem_range.mp (hl₁ ▸ List.mem_append_right pre List.mem_cons_self)
  have hapre : a ∉ pre := by
    intro hm
    have hnd : (pre ++ a :: rest).Nodup := hl₁ ▸ List.nodup_range
    exact (List.nodup_append.mp hnd).2.2 a hm a List.mem_cons_self rfl
  have hmem : ∀ f, f ∈ pre ++ [a] ↔ f ∈ pre ∨ f = a := fun f => by simp
  split
  · next hK =>
    refine triple_pure _ s₁ hi₁ _ _ ⟨fun f v h => ?_, fun f => ?_, hp₁, hn₁⟩
    · obtain ⟨h1, h2⟩ := hm₁ f v h
      exact ⟨List.mem_append_left _ h1, h2⟩
    · rw [hk₁ f]
      by_cases hfa : f = a
      · subst hfa
        rw [hK]
        simp
      · have : decide (f ∈ pre ++ [a]) = decide (f ∈ pre) := by simp [hfa]
        rw [this]
  · next hK =>
    have hK' : (c.isK (a + 32) || c.isK (a + 40) || c.isK (a + 48)) = false := Bool.eq_false_iff.mpr hK
    obtain ⟨⟨hK5, hK6⟩, hK7⟩ := (Bool.or_eq_false_iff.mp hK').imp_left Bool.or_eq_false_iff.mp
    have hq5 := e1_mem_sq (c := c) (q := a + 32) (by omega) hK5
    have hq6 := e1_mem_sq (c := c) (q := a + 40) (by omega) hK6
    have hq7 := e1_mem_sq (c := c) (q := a + 48) (by omega) hK7
    refine triple_bind (e1_newVar s₁ hi₁ _ (.ep a) (fun _ _ h => VDef.noConfusion h)) ?_
    intro v s₂ hi₂ he₂ _ hq₂
    obtain ⟨rfl, hd₂, hn₂, hv₂⟩ := hq₂
    refine triple_bind (e1_emit s₂ hi₂ .ep (by decide) _) ?_
    intro _ s₃ hi₃ he₃ _ hq₃
    refine triple_bind (e1_emit s₃ hi₃ .ep (by decide) _) ?_
    intro _ s₄ hi₄ he₄ _ hq₄
    refine triple_bind (e1_emit s₄ hi₄ .ep (by decide) _) ?_
    intro _ s₅ hi₅ he₅ _ hq₅
    have e25 := ext_trans he₃ (ext_trans he₄ he₅)
    have e15 := ext_trans he₂ e25
    have hd₅ := defs_mono e25 hd₂
    refine triple_pure _ s₅ hi₅ _ _ ⟨?_, ?_, ?_, ?_⟩
    · intro f w h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨h1, h2, h3, h4⟩ := hm₁ f w h
        exact ⟨List.mem_append_left _ h1, h2, h3, defs_mono e15 h4⟩
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_append_right _ (List.mem_singleton_self _), ha, (e1_cr_mem s₁.nv hd₅).1,
          (e1_cr_mem s₁.nv hd₅).2⟩
    · intro f
      rw [List.lookup_append, Option.isSome_or, hk₁ f]
      by_cases hfa : f = a
      · subst hfa
        rw [hK']
        simp [List.lookup]
      · have hb : (f == a) = false := beq_false_of_ne hfa
        simp [List.lookup, hfa, hb]
    · rw [List.pairwise_append]
      refine ⟨hp₁, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
      rw [List.mem_singleton] at hy
      subst hy
      intro e
      have e' : x.1 = a := e
      exact hapre (e' ▸ (hm₁ x.1 x.2 hx).1)
    · intro p A hf hg
      have hl₅ := layout_mono (ext_trans he₁ e15) hl
      have hg₃ := good_mono (ext_trans he₄ he₅) hg
      have hg₄ := good_mono he₅ hg
      refine e1_ngs_trans he₁ e15 (hn₁ p A hf (good_mono e15 hg)) ?_
      refine e1_ngs_trans he₂ e25 (e1_ngs_nil hn₂) ?_
      refine e1_ngs_trans he₃ (ext_trans he₄ he₅) (e1_ngs_single hq₃.1 ?_) ?_
      · exact e1_ep_clause hg₃ (layout_mono (ext_trans he₁ (ext_trans he₂ he₃)) hl) hf hq5 (by decide)
          (fun h => by rw [(e1_ep_facts hf ha h).1]; rfl) (defs_mono he₃ hd₂)
      refine e1_ngs_trans he₄ he₅ (e1_ngs_single hq₄.1 ?_) (e1_ngs_single hq₅.1 ?_)
      · exact e1_ep_clause hg₄ (layout_mono (ext_trans he₁ (ext_trans he₂ (ext_trans he₃ he₄))) hl) hf hq6
          (by decide) (fun h => by rw [(e1_ep_facts hf ha h).2.1]; rfl)
          (defs_mono (ext_trans he₃ he₄) hd₂)
      · exact e1_ep_clause hg hl₅ hf hq7 (by decide) (fun h => by rw [(e1_ep_facts hf ha h).2.2]; rfl) hd₅

theorem e1_init_loop (hc : CfgOk c) :
    Triple (forIn c.squares PUnit.unit fun q _ => do
        let L ← forIn (List.range 11) (#[] : Array Int) fun k L => do
          let v ← newVar (VDef.x q k)
          pure (ForInStep.yield (L.push (v : Int)))
        emit .onehot L
        forIn (List.range 11) PUnit.unit fun i _ => do
          forIn (List.range' (i + 1) (10 - i)) PUnit.unit fun j _ => do
            emit .onehot #[-L[i]!, -L[j]!]
            pure (ForInStep.yield PUnit.unit)
          pure (ForInStep.yield PUnit.unit)
        if ((fr q).2 == 0 || (fr q).2 == 7) = true then do
          emit .rank #[-L[0]!]
          emit .rank #[-L[5]!]
          pure (ForInStep.yield PUnit.unit)
        else pure (ForInStep.yield PUnit.unit)) {} [.onehot, .rank]
      fun _ s' => s'.nv = 11 * c.squares.length ∧
        (∀ q ∈ c.squares, ∀ k < 11, s'.defs[11 * c.xIdx q + k]? = some (.x q k)) ∧
        ∀ p A, Fits c p → Good p A s' → NonGateSat A {} s' := by
  have hne : c.kw ≠ c.kb := by
    intro e
    have h := hc.2.2
    rw [e, cheb_self] at h
    omega
  refine triple_forIn _ _ _ {} [.onehot, .rank] (fun pre _ s' => s'.nv = 11 * pre.length ∧
      (∀ q ∈ pre, ∀ k < 11, s'.defs[11 * c.xIdx q + k]? = some (.x q k)) ∧
      ∀ p A, Fits c p → Good p A s' → NonGateSat A {} s') inv_empty
    ⟨rfl, fun q h => (List.not_mem_nil h).elim,
      fun p A _ _ fc hfc => by rw [newCls_self] at hfc; exact (List.not_mem_nil hfc).elim⟩ ?_
  intro pre a rest _ s₁ hl₁ hi₁ he₁ _ hI₁
  obtain ⟨hv₁, hd₁, hn₁⟩ := hI₁
  have hamem : a ∈ c.squares := hl₁ ▸ List.mem_append_right pre List.mem_cons_self
  obtain ⟨ha64, hakw, hakb⟩ := e1_sq_facts hamem
  have hxa : c.xIdx a = pre.length := by
    have hl' : (List.range 64).filter (fun q => !c.isK q) = pre ++ a :: rest := hl₁
    rw [← e1_count hne a, ← e1_filter_prefix _ 64 hl']
  refine triple_bind (e1_x_loop a s₁ hi₁ _) ?_
  intro L s₂ hi₂ he₂ _ hq₂
  obtain ⟨hL, hv₂, hd₂, hn₂⟩ := hq₂
  refine triple_bind (e1_emitIn s₂ hi₂ (by decide) (List.mem_cons_self) L) ?_
  intro _ s₃ hi₃ he₃ _ hq₃
  obtain ⟨hn₃, hv₃⟩ := hq₃
  refine triple_bind (triple_mono (e1_pairs s₃ hi₃ 11 .onehot (by decide) (fun i => L[i]!))
    (fun g hg => by rw [List.mem_singleton.mp hg]; exact List.mem_cons_self) (fun _ _ _ _ h => h)) ?_
  intro _ s₄ hi₄ he₄ _ hq₄
  obtain ⟨hv₄, hn₄⟩ := hq₄
  have e24 := ext_trans he₃ he₄
  have hd₄ : ∀ k < 11, s₄.defs[s₁.nv + k]? = some (.x a k) := fun k hk => defs_mono e24 (hd₂ k hk)
  have hpre : ∀ (s' : St), Ext s₄ s' → s'.nv = s₄.nv → Inv s' →
      (∀ p A, Fits c p → Good p A s' → NonGateSat A s₄ s') →
      (s'.nv = 11 * (pre ++ [a]).length ∧
        (∀ q ∈ pre ++ [a], ∀ k < 11, s'.defs[11 * c.xIdx q + k]? = some (.x q k)) ∧
        ∀ p A, Fits c p → Good p A s' → NonGateSat A {} s') := by
    intro s' he' hv' _ hN'
    have e1' := ext_trans (ext_trans he₂ e24) he'
    refine ⟨?_, ?_, ?_⟩
    · rw [hv', hv₄, hv₃, hv₂, hv₁, List.length_append]
      simp only [List.length_singleton]
      omega
    · intro q hq k hk
      rcases List.mem_append.mp hq with hq | hq
      · exact defs_mono e1' (hd₁ q hq k hk)
      · rw [List.mem_singleton.mp hq, hxa, ← hv₁]
        exact defs_mono he' (hd₄ k hk)
    · intro p A hf hg
      have hg₄ := good_mono he' hg
      refine e1_ngs_trans he₁ e1' (hn₁ p A hf (good_mono e1' hg)) ?_
      refine e1_ngs_trans (ext_trans he₂ e24) he' ?_ (hN' p A hf hg)
      refine e1_ngs_trans he₂ e24 (e1_ngs_nil hn₂) ?_
      refine e1_ngs_trans he₃ he₄ (e1_ngs_single hn₃ ?_) ?_
      · show L.any (litVal A) = true
        have hk0 := (fits_kings hf).2.2 a ha64 hakw hakb
        rw [← Array.any_toList, hL]
        exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, List.mem_range.mpr hk0, rfl⟩,
          by rw [e1_xval hg₄ (hd₄ _ hk0)]; simp⟩
      · intro fc hfc _
        obtain ⟨i, j, hij, hj, rfl⟩ := hn₄ fc hfc
        show Clause.sat A #[-L[i]!, -L[j]!] = true
        rw [e1_getL hL (by omega), e1_getL hL hj, e1_sat2, litValNeg (by omega), litValNeg (by omega),
          e1_xval hg₄ (hd₄ i (by omega)), e1_xval hg₄ (hd₄ j hj)]
        cases h1 : (symOf (p.board (toSq a)) == i)
        · rfl
        · cases h2 : (symOf (p.board (toSq a)) == j)
          · rfl
          · exfalso
            have := (beq_iff_eq.mp h1).symm.trans (beq_iff_eq.mp h2)
            omega
  split
  · next hr =>
    refine triple_bind (e1_emitIn s₄ hi₄ (by decide) (List.mem_cons_of_mem _ List.mem_cons_self) _) ?_
    intro _ s₅ hi₅ he₅ _ hq₅
    refine triple_bind (e1_emitIn s₅ hi₅ (by decide) (List.mem_cons_of_mem _ List.mem_cons_self) _) ?_
    intro _ s₆ hi₆ he₆ _ hq₆
    refine triple_pure _ s₆ hi₆ _ _ (hpre s₆ (ext_trans he₅ he₆) (hq₆.2.trans hq₅.2) hi₆ ?_)
    intro p A hf hg
    have hg₄ := good_mono (ext_trans he₅ he₆) hg
    have hrk := e1_rank ha64 hr
    refine e1_ngs_trans he₅ he₆ (e1_ngs_single hq₅.1 ?_) (e1_ngs_single hq₆.1 ?_)
    · rw [e1_getL hL (by decide), e1_sat1, litValNeg (by omega), e1_xval hg₄ (hd₄ 0 (by decide))]
      cases h1 : (symOf (p.board (toSq a)) == 0)
      · rfl
      · exfalso
        exact hf.1.noBackPawn (toSq a) .white hrk (e1_sym0 (beq_iff_eq.mp h1))
    · rw [e1_getL hL (by decide), e1_sat1, litValNeg (by omega), e1_xval hg₄ (hd₄ 5 (by decide))]
      cases h1 : (symOf (p.board (toSq a)) == 5)
      · rfl
      · exfalso
        exact hf.1.noBackPawn (toSq a) .black hrk (e1_sym5 (beq_iff_eq.mp h1))
  · refine triple_pure _ s₄ hi₄ _ _ (hpre s₄ (ext_refl s₄) rfl hi₄ ?_)
    intro p A _ _ fc hfc
    rw [newCls_self] at hfc
    exact (List.not_mem_nil hfc).elim

theorem initPhase_spec (hc : CfgOk c) :
    Triple c.initPhase {} [.onehot, .rank] fun _ s' => Layout c s' ∧ s'.nv = 11 * c.squares.length ∧
      ∀ p A, Fits c p → Good p A s' → NonGateSat A {} s' := by
  unfold Cfg.initPhase
  dsimp only
  refine triple_bind (e1_init_loop c hc) ?_
  intro _ s₁ hi₁ _ _ hq₁
  obtain ⟨hv₁, hd₁, hn₁⟩ := hq₁
  refine triple_pure _ s₁ hi₁ _ _ ⟨fun q hq k hk => ⟨?_, ?_⟩, hv₁, hn₁⟩
  · show (0 : Int) < ((1 + 11 * c.xIdx q + k : Nat) : Int)
    omega
  · show s₁.defs[((1 + 11 * c.xIdx q + k : Nat) : Int).toNat - 1]? = _
    rw [Int.toNat_natCast, show 1 + 11 * c.xIdx q + k - 1 = 11 * c.xIdx q + k by omega]
    exact hd₁ q hq k hk

theorem startPhase_spec (hc : CfgOk c) (s : St) (hs : Inv s) (hl : Layout c s) :
    Triple c.startPhase s [.start] fun _ s' => ∀ p A, Fits c p → Good p A s' → NonGateSat A s s' := by
  unfold Cfg.startPhase
  refine triple_bind (e1_widen [.start] (compile_spec s hs _ (e3_attW_bounded hs hl c.kb [] [] [] c.kw))) ?_
  intro w s₁ hi₁ he₁ _ hq₁
  obtain ⟨⟨hwb, hwe⟩, ho₁⟩ := hq₁
  refine triple_bind (require_spec s₁ hi₁ .start (by decide) w) ?_
  intro _ s₂ hi₂ he₂ _ hq₂
  refine triple_bind (e1_widen [.start] (compile_spec s₂ hi₂ _ (e3_attB_bounded hi₂ (layout_mono (ext_trans he₁ he₂) hl) c.kw [] [] []))) ?_
  intro a s₃ hi₃ he₃ _ hq₃
  obtain ⟨⟨hab, hae⟩, ho₃⟩ := hq₃
  refine triple_mono (require_spec s₃ hi₃ .start (by decide) _) (fun f hf => hf) ?_
  intro _ s₄ _ he₄ hq₄ p A hf hg
  have hl₃ := layout_mono (ext_trans (ext_trans he₁ he₂) he₃) hl
  refine e1_ngs_trans (ext_trans he₁ he₂) (ext_trans he₃ he₄)
    (e1_ngs_trans he₁ he₂ (e1_ngs_gate ho₁) (e1_ngs_req hq₂ ?_))
    (e1_ngs_trans he₃ he₄ (e1_ngs_gate ho₃) (e1_ngs_req hq₄ ?_))
  · rw [hwe p A (good_mono (ext_trans he₂ (ext_trans he₃ he₄)) hg)]
    show (!(c.attW c.kb [] [] []).eval A) = true
    rw [e1_attW_start hf (good_mono (ext_trans he₂ (ext_trans he₃ he₄)) hg) (layout_mono he₁ hl)]
    rfl
  · have hg₃ := good_mono he₄ hg
    have hev : a.eval A = c.chk := by rw [hae p A hg₃, e1_attB_start hf hg₃ hl₃]
    cases hck : c.chk
    · rw [if_neg (by simp), a6_neg_eval A hab, hev, hck]
      rfl
    · rw [if_pos rfl, hev, hck]

theorem epPhase_spec (hc : CfgOk c) (s : St) (hs : Inv s) (hl : Layout c s) :
    Triple c.epPhase s [.ep] fun ep s' =>
      (∀ f v, (f, v) ∈ ep → f < 8 ∧ 0 < v ∧ s'.defs[v.toNat - 1]? = some (.ep f)) ∧
      (∀ f < 8, (ep.lookup f).isSome = !(c.isK (f + 32) || c.isK (f + 40) || c.isK (f + 48))) ∧
      ∀ p A, Fits c p → Good p A s' → NonGateSat A s s' := by
  unfold Cfg.epPhase
  dsimp only
  refine triple_bind (e1_ep_loop c s hs hl) ?_
  intro ep s₁ hi₁ he₁ _ hq₁
  obtain ⟨hm₁, hk₁, hp₁, hn₁⟩ := hq₁
  refine triple_bind (e1_pairs s₁ hi₁ (ep.map (fun x => x.snd)).length .ep (by decide)
    (fun i => (ep.map (fun x => x.snd))[i]!)) ?_
  intro _ s₂ hi₂ he₂ _ hq₂
  obtain ⟨-, hc₂⟩ := hq₂
  refine triple_pure _ s₂ hi₂ _ _ ⟨fun f v h => ?_, fun f hf => ?_, fun p A hf hg => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hm₁ f v h
    exact ⟨h1, h2, defs_mono he₂ h3⟩
  · rw [hk₁ f, decide_eq_true (List.mem_range.mpr hf)]
    rfl
  · refine e1_ngs_trans he₁ he₂ (hn₁ p A hf (good_mono he₂ hg)) ?_
    intro fc hfc _
    obtain ⟨i, j, hij, hj, rfl⟩ := hc₂ fc hfc
    rw [List.length_map] at hj
    have hi : i < ep.length := by omega
    have ei : (ep.map (fun x => x.snd))[i]! = ep[i].2 := by
      rw [getElem!_pos _ _ (by rw [List.length_map]; exact hi), List.getElem_map]
    have ej : (ep.map (fun x => x.snd))[j]! = ep[j].2 := by
      rw [getElem!_pos _ _ (by rw [List.length_map]; exact hj), List.getElem_map]
    show Clause.sat A #[-((ep.map (fun x => x.snd))[i]!), -((ep.map (fun x => x.snd))[j]!)] = true
    rw [ei, ej, e1_sat2]
    obtain ⟨fi, vi, hdi⟩ := hm₁ ep[i].1 ep[i].2 (List.getElem_mem hi)
    obtain ⟨fj, vj, hdj⟩ := hm₁ ep[j].1 ep[j].2 (List.getElem_mem hj)
    have hg₁ := good_mono he₂ hg
    rw [litValNeg (by omega), litValNeg (by omega), e1_ep_val hg₁ vi hdi, e1_ep_val hg₁ vj hdj]
    have hne : ep[i].1 ≠ ep[j].1 := List.pairwise_iff_getElem.mp hp₁ i j hi hj hij
    cases h1 : (p.ep == some (toSq (ep[i].1 + 40)))
    · rfl
    · cases h2 : (p.ep == some (toSq (ep[j].1 + 40)))
      · rfl
      · exfalso
        have e := (beq_iff_eq.mp h1).symm.trans (beq_iff_eq.mp h2)
        exact hne (by have := toSq_inj_of_lt (by omega) (by omega) (Option.some.inj e); omega)

theorem crPhase_spec (hc : CfgOk c) (s : St) (hs : Inv s) (hl : Layout c s) :
    Triple c.crPhase s [.castle] fun cr s' =>
      (∀ b v, (b, v) ∈ cr → 0 < v ∧ s'.defs[v.toNat - 1]? = some (.cr b)) ∧
      (∀ b, (cr.lookup b).isSome = (c.kw == E1 && !c.chk && (if b then H1 else A1) != c.kb)) ∧
      ∀ p A, Fits c p → Good p A s' → NonGateSat A s s' := by
  unfold Cfg.crPhase
  split
  · next hcond =>
    dsimp only
    rw [List.forIn_cons, bind_assoc]
    refine triple_bind (e1_cr_body c true H1 [] s hs) ?_
    intro r s₁ hi₁ he₁ _ hq₁
    obtain ⟨rfl, hd₁, hv₁, hn₁⟩ := hq₁
    dsimp only
    rw [List.forIn_cons, bind_assoc]
    refine triple_bind (e1_cr_body c false A1 _ s₁ hi₁) ?_
    intro r s₂ hi₂ he₂ _ hq₂
    obtain ⟨rfl, hd₂, hv₂, hn₂⟩ := hq₂
    dsimp only
    rw [List.forIn_nil, pure_bind]
    have hkw : c.kw = E1 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).1
    have hl₂ := layout_mono (ext_trans he₁ he₂) hl
    refine triple_pure _ s₂ hi₂ _ _ ⟨?_, ?_, ?_⟩
    · intro b v hbv
      cases h1 : (H1 != c.kb) <;> cases h2 : (A1 != c.kb) <;>
        simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.cons_append, List.mem_cons,
          Prod.mk.injEq, List.not_mem_nil, or_false] at hbv
      · obtain ⟨rfl, rfl⟩ := hbv
        exact e1_cr_mem s₁.nv (hd₂ h2)
      · obtain ⟨rfl, rfl⟩ := hbv
        exact e1_cr_mem s.nv (defs_mono he₂ (hd₁ h1))
      · rcases hbv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact e1_cr_mem s.nv (defs_mono he₂ (hd₁ h1))
        · exact e1_cr_mem s₁.nv (hd₂ h2)
    · intro b
      rw [hcond, Bool.true_and]
      cases b <;> cases h1 : (H1 != c.kb) <;> cases h2 : (A1 != c.kb) <;>
        simp [List.lookup, h1, h2]
    · intro p A hf hg fc hfc _
      rw [newCls_trans he₁ he₂, List.mem_append] at hfc
      rcases hfc with h | h
      · obtain ⟨h1, rfl⟩ := hn₁ fc h
        exact e1_cr_sat hf hg hl₂ hkw true H1 rfl (bne_iff_ne.mp h1) s.nv (defs_mono he₂ (hd₁ h1))
      · obtain ⟨h2, rfl⟩ := hn₂ fc h
        exact e1_cr_sat hf hg hl₂ hkw false A1 rfl (bne_iff_ne.mp h2) s₁.nv (hd₂ h2)
  · next hcond =>
    dsimp only
    refine triple_pure _ s hs _ _ ⟨fun b v h => (List.not_mem_nil h).elim, fun b => ?_, fun p A _ _ fc hfc => ?_⟩
    · rw [Bool.eq_false_iff.mpr hcond]
      rfl
    · rw [newCls_self] at hfc
      exact (List.not_mem_nil hfc).elim

section E2H

variable {c : Cfg} {p : Pos} {A : Assignment} {s : St}

theorem eval_lit_xv (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (q k : Nat)
    (hq : q ∈ c.squares) (hk : k < 11) :
    (Wire.lit (c.xv q k)).eval A = (symOf (p.board (toSq q)) == k) := by
  obtain ⟨hpos, hd⟩ := hl q hq k hk
  obtain ⟨hi, hd2⟩ := Array.getElem?_eq_some_iff.mp hd
  have hA := hg _ hi
  rw [hd2] at hA
  show litVal A (c.xv q k) = _
  show (if 0 < c.xv q k then A (c.xv q k).toNat else !A (c.xv q k).natAbs) =
    (symOf (p.board (toSq q)) == k)
  rw [if_pos hpos]
  have ht : (c.xv q k).toNat = 1 + 11 * c.xIdx q + k := Int.toNat_natCast _
  have e : (c.xv q k).toNat - 1 + 1 = (c.xv q k).toNat := by omega
  rw [← e]
  exact hA

theorem symOf_eq_kindOf (o : Option Piece) (white : Bool) (k : Nat) (hk : k < 5) :
    (symOf o == (if white then k else k + 5)) = (o == some ⟨colOf white, kindOf k⟩) := by
  cases o with
  | none =>
    cases white <;> rcases k with _ | _ | _ | _ | _ | k <;>
      first | decide | exact absurd hk (by omega)
  | some pc =>
    obtain ⟨col, kd⟩ := pc
    cases col <;> cases kd <;> cases white <;>
      rcases k with _ | _ | _ | _ | _ | k <;> first | decide | exact absurd hk (by omega)

theorem symOf_eq_bishop (o : Option Piece) (white : Bool) :
    (symOf o == (if white then 2 else 7)) = (o == some ⟨colOf white, .bishop⟩) := by
  cases o with
  | none => cases white <;> decide
  | some pc =>
    obtain ⟨col, kd⟩ := pc
    cases col <;> cases kd <;> cases white <;> decide

theorem parity_toSq (q : Nat) (hq : q < 64) : parity (toSq q) = (q % 8 + q / 8) % 2 := by
  show ((q % 64) % 8 + (q % 64) / 8) % 2 = (q % 8 + q / 8) % 2
  rw [Nat.mod_eq_of_lt hq]

theorem fr_sum (q : Nat) : ((fr q).1 + (fr q).2) = ((q % 8 + q / 8 : Nat) : Int) := by
  show ((↑(q % 8) : Int) + ↑(q / 8)) = ↑(q % 8 + q / 8)
  rw [Int.natCast_add]

theorem fr_parity (q par : Nat) (hq : q < 64) :
    (((fr q).1 + (fr q).2) % 2 == (par : Int)) = (parity (toSq q) == par) := by
  have h1 : (((fr q).1 + (fr q).2) % 2 : Int) = ((parity (toSq q) : Nat) : Int) := by
    rw [fr_sum q, parity_toSq q hq]
    exact (Int.natCast_emod _ _).symm
  rw [h1]
  by_cases heq : parity (toSq q) = par
  · rw [beq_iff_eq.mpr heq, beq_iff_eq.mpr (by omega : (↑(parity (toSq q)) : Int) = ↑par)]
  · rw [beq_eq_false_iff_ne.mpr heq,
      beq_eq_false_iff_ne.mpr (by omega : (↑(parity (toSq q)) : Int) ≠ ↑par)]

def nkMan (o : Option Piece) (col : Color) : Bool :=
  match o with
  | some pc => (pc.color == col) && (pc.kind != .king)
  | none => false

theorem nkMan_or_king (o : Option Piece) (col : Color) :
    (o.any (·.color == col)) = (nkMan o col || (o == some ⟨col, .king⟩)) := by
  cases o with
  | none => cases col <;> decide
  | some pc =>
    obtain ⟨c1, kd⟩ := pc
    cases c1 <;> cases kd <;> cases col <;> decide

theorem nkMan_ne_king (o : Option Piece) (col : Color) :
    nkMan o col = true → (o == some ⟨col, .king⟩) = true → False := by
  intro hnk hk
  cases o with
  | none => exact Bool.noConfusion hnk
  | some pc =>
    obtain ⟨c1, kd⟩ := pc
    have h2 := beq_iff_eq.mp hk
    injection h2 with h2'
    rw [Piece.mk.injEq] at h2'
    obtain ⟨-, rfl⟩ := h2'
    have h3 : ((c1 == col) && (Kind.king != Kind.king)) = true := hnk
    rw [bne_self_eq_false, Bool.and_false] at h3
    exact Bool.noConfusion h3

theorem nodup_map_toSq {l : List Nat} (hl : ∀ q ∈ l, q < 64) (hn : l.Nodup) :
    (l.map toSq).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons]
    obtain ⟨ha, hn'⟩ := List.nodup_cons.mp hn
    refine ⟨?_, ih (fun q hq => hl q (List.mem_cons_of_mem a hq)) hn'⟩
    intro hbm
    rw [List.mem_map] at hbm
    obtain ⟨x, hx, hxe⟩ := hbm
    have hax : a < 64 := hl a List.mem_cons_self
    have hxx : x < 64 := hl x (List.mem_cons_of_mem a hx)
    have hv := Fin.ext_iff.mp hxe
    rw [toSq_val_of_lt x hxx, toSq_val_of_lt a hax] at hv
    exact ha (hv ▸ hx)

theorem count_bridge (g : Nat → Bool) (G : Sq → Bool)
    (hgG : ∀ q, q ∈ c.squares → g q = G (toSq q))
    (hkw : G (toSq c.kw) = false) (hkb : G (toSq c.kb) = false) :
    (allSq.filter G).length = (c.squares.filter g).length := by
  have hnd1 : (allSq.filter G).Nodup :=
    List.Nodup.sublist List.filter_sublist (List.nodup_finRange 64)
  have hsqnodup : (c.squares.filter g).Nodup := by
    show (((List.range 64).filter fun q => !c.isK q).filter g).Nodup
    exact List.Nodup.sublist List.filter_sublist
      (List.Nodup.sublist List.filter_sublist List.nodup_range)
  have hnd2 : ((c.squares.filter g).map toSq).Nodup := by
    refine nodup_map_toSq ?_ hsqnodup
    intro q hq
    have h1 : q ∈ c.squares := List.mem_filter.mp hq |>.1
    show q < 64
    have h2 : q ∈ (List.range 64).filter (fun q => !c.isK q) := h1
    exact List.mem_range.mp (List.mem_filter.mp h2).1
  have hmem' : ∀ x, x ∈ allSq.filter G ↔ x ∈ (c.squares.filter g).map toSq := by
    intro a
    constructor
    · intro h
      obtain ⟨hm, hsat⟩ := List.mem_filter.mp h
      rw [List.mem_map]
      have hmem : a.val ∈ c.squares := by
        have h1 : a.val ∈ List.range 64 := List.mem_range.mpr a.isLt
        show a.val ∈ (List.range 64).filter fun q => !c.isK q
        rw [List.mem_filter]
        refine ⟨h1, ?_⟩
        cases hK : c.isK a.val with
        | true =>
          unfold Cfg.isK at hK
          rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hK
          rcases hK with hK | hK
          · have hq : a = toSq c.kw := by
              have h2 := congrArg toSq hK
              rw [toSq_val] at h2
              exact h2
            rw [hq, hkw] at hsat
            exact Bool.noConfusion hsat
          · have hq : a = toSq c.kb := by
              have h2 := congrArg toSq hK
              rw [toSq_val] at h2
              exact h2
            rw [hq, hkb] at hsat
            exact Bool.noConfusion hsat
        | false => rfl
      refine ⟨a.val, ?_, toSq_val a⟩
      rw [List.mem_filter]
      refine ⟨hmem, ?_⟩
      rw [hgG a.val hmem, toSq_val]
      exact hsat
    · intro h
      rw [List.mem_map] at h
      obtain ⟨q, hq, hqe⟩ := h
      rw [List.mem_filter] at hq
      obtain ⟨hqsq, hqev⟩ := hq
      rw [List.mem_filter]
      constructor
      · rw [← hqe]
        exact List.mem_finRange _
      · rw [← hqe, ← hgG q hqsq]
        exact hqev
  have h1sub := List.Nodup.length_le_of_subset hnd1 (fun x hx => (hmem' x).mp hx)
  have h2sub := List.Nodup.length_le_of_subset hnd2 (fun x hx => (hmem' x).mpr hx)
  rw [List.length_map] at h1sub h2sub
  omega

theorem filter_mono_length (l : List α) (P Q : α → Bool) (hPQ : ∀ x ∈ l, P x = true → Q x = true) :
    (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih =>
    rw [List.filter_cons, List.filter_cons]
    by_cases ha : P a = true
    · rw [if_pos ha, if_pos (hPQ a List.mem_cons_self ha), List.length_cons, List.length_cons]
      have ih' := ih fun x hx => hPQ x (List.mem_cons_of_mem a hx)
      omega
    · rw [if_neg ha]
      by_cases hb : Q a = true
      · rw [if_pos hb, List.length_cons]
        have ih' := ih fun x hx => hPQ x (List.mem_cons_of_mem a hx)
        omega
      · rw [if_neg hb]
        exact ih fun x hx => hPQ x (List.mem_cons_of_mem a hx)

theorem filter_or_disj_length (l : List α) (P Q : α → Bool)
    (hPQ : ∀ x ∈ l, P x = true → Q x = true → False) :
    (l.filter fun x => P x || Q x).length = (l.filter P).length + (l.filter Q).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons, List.filter_cons, List.filter_cons]
    have hih := ih fun x hx => hPQ x (List.mem_cons_of_mem a hx)
    by_cases hp : P a = true
    · have hq : Q a = false := by
        cases hQ : Q a with
        | true => exact absurd hp fun hp' => hPQ a List.mem_cons_self hp' hQ
        | false => rfl
      rw [if_pos (show (P a || Q a) = true by rw [hp, Bool.true_or]), if_pos hp,
        if_neg (show ¬ (Q a = true) by rw [hq]; exact fun h => Bool.noConfusion h)]
      simp only [List.length_cons]
      rw [hih]
      omega
    · have hpf : P a = false := Bool.eq_false_of_ne_true hp
      by_cases hq : Q a = true
      · rw [if_pos (show (P a || Q a) = true by rw [hpf, hq, Bool.false_or]), if_neg hp, if_pos hq]
        simp only [List.length_cons]
        rw [hih]
        omega
      · have hqf : Q a = false := Bool.eq_false_of_ne_true hq
        rw [if_neg (show ¬ (P a || Q a) = true by rw [hpf, hqf]; exact fun h => Bool.noConfusion h),
          if_neg hp, if_neg hq, hih]

theorem filter_eval_range'_congr : ∀ (l : List Wire) (start m : Nat) (g : Nat → Bool) (A : Assignment),
    l.length = m → (∀ i < m, l[i]!.eval A = g (start + i)) →
    (l.filter (·.eval A)).length = ((List.range' start m).filter g).length := by
  intro l
  induction l with
  | nil =>
    intro start m g A hl _
    cases m with
    | zero => rfl
    | succ m => rw [List.length_nil] at hl; omega
  | cons a l ih =>
    intro start m g A hl h
    cases m with
    | zero => rw [List.length_cons] at hl; omega
    | succ m =>
      rw [List.filter_cons, List.range'_succ, List.filter_cons]
      have h0 : a.eval A = g start := by
        have hh := h 0 (Nat.zero_lt_succ m)
        rwa [List.getElem!_cons_zero, Nat.add_zero] at hh
      rw [h0]
      have hlm : l.length = m := by
        rw [List.length_cons] at hl
        omega
      have hih : (l.filter (·.eval A)).length = ((List.range' (start + 1) m).filter g).length :=
        ih (start + 1) m g A hlm (fun i hi => by
          have hh := h (i + 1) (Nat.succ_lt_succ hi)
          rwa [List.getElem!_cons_succ, show start + (i + 1) = start + 1 + i from by omega] at hh)
      by_cases hg0 : g start = true
      · rw [if_pos hg0, if_pos hg0, List.length_cons, List.length_cons, hih]
      · rw [if_neg hg0, if_neg hg0, hih]

theorem count_le_range' (start m N : Nat) :
    ((List.range' start m).filter fun j => decide (j ≤ N)).length = min (start + m) (N + 1) - start := by
  induction m generalizing start with
  | zero =>
    rw [List.range'_zero, List.filter_nil]
    show 0 = min (start + 0) (N + 1) - start
    omega
  | succ m ih =>
    rw [List.range'_succ, List.filter_cons]
    by_cases h : start ≤ N
    · rw [decide_eq_true_iff.mpr h, if_pos rfl, List.length_cons, ih]
      omega
    · rw [decide_eq_false_iff_not.mpr h, if_neg (fun hh => Bool.noConfusion hh), ih]
      omega

theorem nkMan_block_count (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (white : Bool) (q : Nat)
    (hq : q ∈ c.squares) :
    (((List.range 5).map fun k => Wire.lit (c.xv q (if white then k else k + 5))).filter (·.eval A)).length =
      (if nkMan (p.board (toSq q)) (colOf white) then 1 else 0) := by
  have e : ∀ k : Nat, k < 5 →
      (Wire.lit (c.xv q (if white then k else k + 5))).eval A =
        (symOf (p.board (toSq q)) == (if white then k else k + 5)) :=
    fun k hk => eval_lit_xv hf hg hl q _ hq (by
      cases white with
      | true => show k < 11; omega
      | false => show k + 5 < 11; omega)
  show (([Wire.lit (c.xv q (if white then 0 else 0 + 5)), Wire.lit (c.xv q (if white then 1 else 1 + 5)),
      Wire.lit (c.xv q (if white then 2 else 2 + 5)), Wire.lit (c.xv q (if white then 3 else 3 + 5)),
      Wire.lit (c.xv q (if white then 4 else 4 + 5))]).filter (·.eval A)).length = _
  rw [List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons,
    List.filter_nil]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide)]
  cases hb : p.board (toSq q) with
  | none => cases white <;> first | rfl | decide | simp
  | some pc =>
    obtain ⟨c1, kd⟩ := pc
    cases c1 <;> cases kd <;> cases white <;> first | rfl | decide | simp

theorem flatMap_men_count (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (white : Bool)
    (l : List Nat) (hlq : ∀ q ∈ l, q ∈ c.squares) :
    ((l.flatMap fun q => (List.range 5).map fun k => Wire.lit (c.xv q (if white then k else k + 5))).filter
        (·.eval A)).length =
      (l.filter fun q => nkMan (p.board (toSq q)) (colOf white)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.filter_append, List.length_append,
      ih (fun q hq => hlq q (List.mem_cons_of_mem a hq))]
    by_cases hb : nkMan (p.board (toSq a)) (colOf white) = true
    · rw [List.filter_cons_of_pos (p := fun q => nkMan (p.board (toSq q)) (colOf white)) (a := a)
        (l := l) hb, List.length_cons]
      rw [nkMan_block_count hf hg hl white a (hlq a List.mem_cons_self), if_pos hb]
      omega
    · rw [List.filter_cons_of_neg (p := fun q => nkMan (p.board (toSq q)) (colOf white)) (a := a)
        (l := l) hb]
      rw [nkMan_block_count hf hg hl white a (hlq a List.mem_cons_self), if_neg hb]
      omega

end E2H

theorem counter_drop_count (cnt : Array Wire) (L : List Wire) (k base : Nat) (A : Assignment)
    (hsz : cnt.size = k + 1) (hc : ∀ j ≤ k, cnt[j]!.eval A = decide (j ≤ (L.filter (·.eval A)).length))
    (hL : (L.filter (·.eval A)).length ≤ k) :
    ((cnt.toList.drop (base + 1)).filter (·.eval A)).length = (L.filter (·.eval A)).length - base := by
  have hle : (cnt.toList.drop (base + 1)).length = k - base := by
    rw [List.length_drop, Array.length_toList, hsz]
    omega
  have hel : ∀ i < k - base, (cnt.toList.drop (base + 1))[i]!.eval A =
      decide (base + 1 + i ≤ (L.filter (·.eval A)).length) := by
    intro i hi
    have hb1 : i < (cnt.toList.drop (base + 1)).length := by
      rw [List.length_drop, Array.length_toList, hsz]
      omega
    rw [getElem!_pos (cnt.toList.drop (base + 1)) i hb1, List.getElem_drop, Array.getElem_toList,
      ← a7_getElem!_eq_getElem (by rw [hsz]; omega : base + 1 + i < cnt.size)]
    exact hc (base + 1 + i) (by omega)
  have h1 := filter_eval_range'_congr (cnt.toList.drop (base + 1)) (base + 1) (k - base)
    (fun j => decide (j ≤ (L.filter (·.eval A)).length)) A hle hel
  rw [h1, count_le_range']
  omega

theorem material_lits_count {p : Pos} {A : Assignment} {s : St} (hf : Fits c p) (hg : Good p A s)
    (hl : Layout c s) (white : Bool) (k : Nat) (hk : k < 5) :
    ((c.squares.map fun q => Wire.lit (c.xv q (if white then k else k + 5))).filter (·.eval A)).length =
      cnt p.board (colOf white) (kindOf k) := by
  rw [List.filter_map, List.length_map]
  show (c.squares.filter ((·.eval A) ∘ fun q => Wire.lit (c.xv q (if white then k else k + 5)))).length =
    (allSq.filter fun s => p.board s == some ⟨colOf white, kindOf k⟩).length
  refine (count_bridge ((·.eval A) ∘ fun q => Wire.lit (c.xv q (if white then k else k + 5)))
    (fun s => p.board s == some ⟨colOf white, kindOf k⟩) ?_ ?_ ?_).symm
  · intro q hq
    show (Wire.lit (c.xv q (if white then k else k + 5))).eval A =
      (p.board (toSq q) == some ⟨colOf white, kindOf k⟩)
    rw [eval_lit_xv hf hg hl q _ hq (by
      cases white with
      | true => show k < 11; omega
      | false => show k + 5 < 11; omega)]
    exact symOf_eq_kindOf _ white k hk
  · show (p.board (toSq c.kw) == some ⟨colOf white, kindOf k⟩) = false
    rw [(fits_kings hf).1]
    cases white <;> rcases k with _ | _ | _ | _ | _ | k <;>
      first | decide | exact absurd hk (by omega)
  · show (p.board (toSq c.kb) == some ⟨colOf white, kindOf k⟩) = false
    rw [(fits_kings hf).2.1]
    cases white <;> rcases k with _ | _ | _ | _ | _ | k <;>
      first | decide | exact absurd hk (by omega)

theorem material_bishop_count {p : Pos} {A : Assignment} {s : St} (hf : Fits c p) (hg : Good p A s)
    (hl : Layout c s) (white : Bool) (par : Nat) (hpar : par < 2) :
    (((c.squares.filter fun q => ((fr q).1 + (fr q).2) % 2 == par).map fun q =>
        Wire.lit (c.xv q (if white then 2 else 7))).filter (·.eval A)).length =
      cntB p.board (colOf white) par := by
  rw [List.filter_map, List.length_map, List.filter_filter]
  show (c.squares.filter fun a => ((Wire.lit (c.xv a (if white then 2 else 7))).eval A) &&
      (((fr a).1 + (fr a).2) % 2 == (par : Int))).length =
    (allSq.filter fun s => (p.board s == some ⟨colOf white, .bishop⟩) && (parity s == par)).length
  refine (count_bridge (fun a => ((Wire.lit (c.xv a (if white then 2 else 7))).eval A) &&
      (((fr a).1 + (fr a).2) % 2 == (par : Int)))
    (fun s => (p.board s == some ⟨colOf white, .bishop⟩) && (parity s == par)) ?_ ?_ ?_).symm
  · intro q hq
    have hq64 : q < 64 := List.mem_range.mp (List.mem_filter.mp hq).1
    show (((Wire.lit (c.xv q (if white then 2 else 7))).eval A &&
        (((fr q).1 + (fr q).2) % 2 == (par : Int)))) =
      ((p.board (toSq q) == some ⟨colOf white, .bishop⟩) && (parity (toSq q) == par))
    rw [eval_lit_xv hf hg hl q _ hq (by cases white with | true => decide | false => decide),
      symOf_eq_bishop (p.board (toSq q)) white, fr_parity q par hq64]
  · show (p.board (toSq c.kw) == some ⟨colOf white, .bishop⟩ && parity (toSq c.kw) == par) = false
    rw [(fits_kings hf).1]
    have hb : ((some ⟨.white, .king⟩ : Option Piece) == some ⟨colOf white, .bishop⟩) = false := by
      cases white <;> decide
    rw [hb, Bool.false_and]
  · show (p.board (toSq c.kb) == some ⟨colOf white, .bishop⟩ && parity (toSq c.kb) == par) = false
    rw [(fits_kings hf).2.1]
    have hb : ((some ⟨.black, .king⟩ : Option Piece) == some ⟨colOf white, .bishop⟩) = false := by
      cases white <;> decide
    rw [hb, Bool.false_and]

theorem material_men_count {p : Pos} {A : Assignment} {s : St} (hf : Fits c p) (hg : Good p A s)
    (hl : Layout c s) (white : Bool) :
    ((c.squares.flatMap fun q => (List.range 5).map fun k => Wire.lit (c.xv q (if white then k else k + 5))).filter
        (·.eval A)).length + 1 = men p.board (colOf white) := by
  have hunfold : men p.board (colOf white) =
      (allSq.filter fun s => (p.board s).any (·.color == colOf white)).length := rfl
  rw [hunfold]
  have hsplit : (allSq.filter fun s => (p.board s).any (·.color == colOf white)).length =
      (allSq.filter fun s => nkMan (p.board s) (colOf white) ||
        (p.board s == some ⟨colOf white, .king⟩)).length := by
    apply congrArg List.length
    apply List.filter_congr
    intro x _
    exact nkMan_or_king (p.board x) (colOf white)
  rw [hsplit, filter_or_disj_length allSq (fun s => nkMan (p.board s) (colOf white))
    (fun s => p.board s == some ⟨colOf white, .king⟩)
    (fun x _ => nkMan_ne_king (p.board x) (colOf white))]
  have hb1 : (allSq.filter fun s => nkMan (p.board s) (colOf white)).length =
      (c.squares.filter fun q => nkMan (p.board (toSq q)) (colOf white)).length :=
    count_bridge _ _ (fun _ _ => rfl) (by rw [(fits_kings hf).1]; cases white <;> decide)
      (by rw [(fits_kings hf).2.1]; cases white <;> decide)
  have hb2 : (allSq.filter fun s => p.board s == some ⟨colOf white, .king⟩).length = 1 := by
    show cnt p.board (colOf white) .king = 1
    exact hf.1.kings _
  rw [hb1, hb2]
  rw [flatMap_men_count hf hg hl white c.squares (fun q hq => hq)]

section E2H2

variable {c : Cfg} {p : Pos} {A : Assignment} {s : St}

theorem nkMan_squares_bound (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (white : Bool) :
    (c.squares.filter fun q => nkMan (p.board (toSq q)) (colOf white)).length ≤ 15 := by
  have hmen := material_men_count c hf hg hl white
  have hflat := flatMap_men_count hf hg hl white c.squares (fun q hq => hq)
  have hmle := hf.1.menLe (colOf white)
  omega

theorem kind_cnt_le_15 (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (white : Bool) (k : Nat)
    (hk : k < 5) : cnt p.board (colOf white) (kindOf k) ≤ 15 := by
  have hcnt : cnt p.board (colOf white) (kindOf k) =
      (allSq.filter fun s => p.board s == some ⟨colOf white, kindOf k⟩).length := rfl
  have hb1 : (allSq.filter fun s => p.board s == some ⟨colOf white, kindOf k⟩).length ≤
      (allSq.filter fun s => nkMan (p.board s) (colOf white)).length := by
    refine filter_mono_length allSq _ _ fun x _ hxx => ?_
    have he := beq_iff_eq.mp hxx
    rw [he]
    show ((colOf white == colOf white) && (kindOf k != Kind.king)) = true
    rw [beq_self_eq_true, Bool.true_and, bne_iff_ne]
    rcases k with _ | _ | _ | _ | _ | k <;> first | decide | exact absurd hk (by omega)
  have hb2 : (allSq.filter fun s => nkMan (p.board s) (colOf white)).length =
      (c.squares.filter fun q => nkMan (p.board (toSq q)) (colOf white)).length :=
    count_bridge _ _ (fun _ _ => rfl) (by rw [(fits_kings hf).1]; cases white <;> decide)
      (by rw [(fits_kings hf).2.1]; cases white <;> decide)
  have hnksq := nkMan_squares_bound hf hg hl white
  omega

theorem bishop_cnt_le_15 (hf : Fits c p) (hg : Good p A s) (hl : Layout c s) (white : Bool)
    (par : Nat) (hpar : par < 2) : cntB p.board (colOf white) par ≤ 15 := by
  have hcnt : cntB p.board (colOf white) par =
      (allSq.filter fun s => (p.board s == some ⟨colOf white, .bishop⟩) && (parity s == par)).length :=
    rfl
  have hb1 : (allSq.filter fun s =>
        (p.board s == some ⟨colOf white, .bishop⟩) && (parity s == par)).length ≤
      (allSq.filter fun s => nkMan (p.board s) (colOf white)).length := by
    refine filter_mono_length allSq _ _ fun x _ hxx => ?_
    rw [Bool.and_eq_true] at hxx
    have he := beq_iff_eq.mp hxx.1
    rw [he]
    show ((colOf white == colOf white) && (Kind.bishop != Kind.king)) = true
    rw [beq_self_eq_true]
    rfl
  have hb2 : (allSq.filter fun s => nkMan (p.board s) (colOf white)).length =
      (c.squares.filter fun q => nkMan (p.board (toSq q)) (colOf white)).length :=
    count_bridge _ _ (fun _ _ => rfl) (by rw [(fits_kings hf).1]; cases white <;> decide)
      (by rw [(fits_kings hf).2.1]; cases white <;> decide)
  have hnksq := nkMan_squares_bound hf hg hl white
  omega

theorem matKindLoop (white : Bool) (s₁ : St) (hinv₁ : Inv s₁) (hl₁ : Layout c s₁) :
    Triple (forIn ([(1, 2), (3, 2), (4, 1)] : List (Nat × Nat)) ([] : List Wire)
      (fun (kb : Nat × Nat) (ex : List Wire) =>
        counter (c.squares.map fun q => Wire.lit (c.xv q (if white then kb.1 else kb.1 + 5))) 15 >>=
          fun cnt => pure (ForInStep.yield (ex ++ cnt.toList.drop (kb.2 + 1))))) s₁ [.material]
      fun ex s' => (∀ w ∈ ex, w.Bounded s'.nv) ∧
        (∀ p A, Fits c p → Good p A s' → (ex.filter (·.eval A)).length =
          (([(1, 2), (3, 2), (4, 1)] : List (Nat × Nat)).map fun kb =>
            cnt p.board (colOf white) (kindOf kb.1) - kb.2).sum) ∧
        (∀ fc ∈ NewCls s₁ s', fc.1 = .material → False) := by
  refine triple_forIn _ _ _ _ [.material]
    (fun (pre : List (Nat × Nat)) (ex : List Wire) (s' : St) => (∀ w ∈ ex, w.Bounded s'.nv) ∧
      (∀ p A, Fits c p → Good p A s' → (ex.filter (·.eval A)).length =
        (pre.map fun kb => cnt p.board (colOf white) (kindOf kb.1) - kb.2).sum) ∧
      (∀ fc ∈ NewCls s₁ s', fc.1 = .material → False))
    hinv₁ ?_ ?_
  · exact ⟨fun w hw => (List.not_mem_nil hw).elim, fun p A _ _ => rfl, fun fc hfc _ => by
      rw [newCls_self] at hfc
      exact (List.not_mem_nil hfc).elim⟩
  · intro pre a rest ex s' hspl hinv' hext' _ hI'
    obtain ⟨hbx, hcx, hinfo⟩ := hI'
    have ham : a ∈ [(1, 2), (3, 2), (4, 1)] := by
      rw [hspl]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨kk, ba⟩ := a
    have hkk : kk < 5 := by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ham
      rcases ham with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
    have hl' : Layout c s' := layout_mono hext' hl₁
    have hbL : ∀ w ∈ (c.squares.map fun q => Wire.lit (c.xv q (if white then kk else kk + 5))),
        w.Bounded s'.nv := by
      intro w hw
      rw [List.mem_map] at hw
      obtain ⟨q, hq, rfl⟩ := hw
      exact layout_bounded hinv' hl' q _ hq (by
        cases white with
        | true => show kk < 11; omega
        | false => show kk + 5 < 11; omega)
    refine triple_mono ?_ (fun f hf => (List.not_mem_nil hf).elim) (fun a s'' _ _ h => h)
    refine triple_bind (counter_spec s' hinv' _ 15 hbL) ?_
    intro cn s₂' hinv₂ hext₂ hof₂ hQc
    obtain ⟨hsz2, hbnd2, hev2⟩ := hQc
    refine triple_pure (ForInStep.yield (ex ++ cn.toList.drop (ba + 1))) s₂' hinv₂ [] _ ?_
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rw [List.mem_append] at hw
      rcases hw with hw | hw
      · exact wire_bounded_mono (by rw [hinv'.nv, hinv₂.nv]; exact hext₂.defs_le) (hbx w hw)
      · exact hbnd2 w (Array.mem_def.mpr (List.mem_of_mem_drop hw))
    · intro p A hfp hg₂
      have hg₁ := good_mono hext₂ hg₂
      have hl₂ := layout_mono hext₂ hl'
      have hNk := material_lits_count c hfp hg₂ hl₂ white kk hkk
      have hle15 : ((c.squares.map fun q => Wire.lit (c.xv q (if white then kk else kk + 5))).filter
            (·.eval A)).length ≤ 15 := by
        rw [hNk]
        exact kind_cnt_le_15 hfp hg₂ hl₂ white kk hkk
      have hseg := counter_drop_count cn _ 15 ba A hsz2 (fun j hj => hev2 p A hg₂ j hj) hle15
      rw [hNk] at hseg
      have hcx' := hcx p A hfp hg₁
      rw [List.filter_append, List.length_append, hcx', hseg, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      show (pre.map fun kb => cnt p.board (colOf white) (kindOf kb.1) - kb.2).sum +
          (cnt p.board (colOf white) (kindOf kk) - ba) =
        (pre.map fun kb => cnt p.board (colOf white) (kindOf kb.1) - kb.2).sum +
          (cnt p.board (colOf white) (kindOf kk) - ba + 0)
      omega
    · intro fc hfc hfam
      rw [newCls_trans hext' hext₂] at hfc
      rcases List.mem_append.mp hfc with hfc | hfc
      · exact hinfo fc hfc hfam
      · rcases List.mem_cons.mp (hof₂ fc hfc) with h | h
        · rw [h] at hfam
          exact Fam.noConfusion hfam
        · exact (List.not_mem_nil h).elim

theorem matBishLoop (white : Bool) (s₂ : St) (hinv₂ : Inv s₂) (hl₂ : Layout c s₂)
    (ex₁ : List Wire) (hbx₁ : ∀ w ∈ ex₁, w.Bounded s₂.nv) :
    Triple (forIn ([0, 1] : List Nat) ex₁
      (fun (colour : Nat) (ex : List Wire) =>
        counter ((c.squares.filter fun q => ((fr q).1 + (fr q).2) % 2 == (colour : Int)).map fun q =>
          Wire.lit (c.xv q (if white then 2 else 7))) 15 >>=
          fun cnt => pure (ForInStep.yield (ex ++ cnt.toList.drop 2)))) s₂ [.material]
      fun ex s' => (∀ w ∈ ex, w.Bounded s'.nv) ∧
        (∀ p A, Fits c p → Good p A s' → (ex.filter (·.eval A)).length =
          (ex₁.filter (·.eval A)).length +
            (([0, 1] : List Nat).map fun par => cntB p.board (colOf white) par - 1).sum) ∧
        (∀ fc ∈ NewCls s₂ s', fc.1 = .material → False) := by
  refine triple_forIn _ _ _ _ [.material]
    (fun (pre : List Nat) (ex : List Wire) (s' : St) => (∀ w ∈ ex, w.Bounded s'.nv) ∧
      (∀ p A, Fits c p → Good p A s' → (ex.filter (·.eval A)).length =
        (ex₁.filter (·.eval A)).length +
          (pre.map fun par => cntB p.board (colOf white) par - 1).sum) ∧
      (∀ fc ∈ NewCls s₂ s', fc.1 = .material → False))
    hinv₂ ?_ ?_
  · exact ⟨hbx₁, fun p A _ _ => rfl, fun fc hfc _ => by
      rw [newCls_self] at hfc
      exact (List.not_mem_nil hfc).elim⟩
  · intro pre a rest ex s' hspl hinv' hext' _ hI'
    obtain ⟨hbx, hcx, hinfo⟩ := hI'
    have ham : a ∈ [0, 1] := by
      rw [hspl]
      exact List.mem_append_right _ List.mem_cons_self
    have hpar : a < 2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ham
      rcases ham with rfl | rfl <;> decide
    have hl' : Layout c s' := layout_mono hext' hl₂
    have hbL : ∀ w ∈ ((c.squares.filter fun q => ((fr q).1 + (fr q).2) % 2 == (a : Int)).map fun q =>
        Wire.lit (c.xv q (if white then 2 else 7))), w.Bounded s'.nv := by
      intro w hw
      rw [List.mem_map] at hw
      obtain ⟨q, hq, rfl⟩ := hw
      exact layout_bounded hinv' hl' q _ (List.mem_filter.mp hq).1 (by cases white <;> decide)
    refine triple_mono ?_ (fun f hf => (List.not_mem_nil hf).elim) (fun a s'' _ _ h => h)
    refine triple_bind (counter_spec s' hinv' _ 15 hbL) ?_
    intro cn s₃' hinv₃ hext₃ hof₃ hQc
    obtain ⟨hsz3, hbnd3, hev3⟩ := hQc
    refine triple_pure (ForInStep.yield (ex ++ cn.toList.drop 2)) s₃' hinv₃ [] _ ?_
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rw [List.mem_append] at hw
      rcases hw with hw | hw
      · exact wire_bounded_mono (by rw [hinv'.nv, hinv₃.nv]; exact hext₃.defs_le) (hbx w hw)
      · exact hbnd3 w (Array.mem_def.mpr (List.mem_of_mem_drop hw))
    · intro p A hfp hg₃
      have hg₁ := good_mono hext₃ hg₃
      have hl₃ := layout_mono hext₃ hl'
      have hNb := material_bishop_count c hfp hg₃ hl₃ white a hpar
      have hle15 : (((c.squares.filter fun q => ((fr q).1 + (fr q).2) % 2 == (a : Int)).map fun q =>
            Wire.lit (c.xv q (if white then 2 else 7))).filter (·.eval A)).length ≤ 15 := by
        rw [hNb]
        exact bishop_cnt_le_15 hfp hg₃ hl₃ white a hpar
      have hseg := counter_drop_count cn _ 15 1 A hsz3 (fun j hj => hev3 p A hg₃ j hj) hle15
      rw [hNb] at hseg
      have hcx' := hcx p A hfp hg₁
      rw [List.filter_append, List.length_append, hcx', hseg, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      show (ex₁.filter (·.eval A)).length +
          (pre.map fun par => cntB p.board (colOf white) par - 1).sum +
          (cntB p.board (colOf white) a - 1) =
        (ex₁.filter (·.eval A)).length +
          ((pre.map fun par => cntB p.board (colOf white) par - 1).sum +
            (cntB p.board (colOf white) a - 1 + 0))
      omega
    · intro fc hfc hfam
      rw [newCls_trans hext' hext₃] at hfc
      rcases List.mem_append.mp hfc with hfc | hfc
      · exact hinfo fc hfc hfam
      · rcases List.mem_cons.mp (hof₃ fc hfc) with h | h
        · rw [h] at hfam
          exact Fam.noConfusion hfam
        · exact (List.not_mem_nil h).elim

end E2H2


theorem materialPhase_spec (hc : CfgOk c) (white : Bool) (s : St) (hs : Inv s) (hl : Layout c s) :
    Triple (c.materialPhase white) s [.material] fun _ s' =>
      ∀ p A, Fits c p → Good p A s' → NonGateSat A s s' := by
  have hbnd0 : ∀ w ∈ (c.squares.flatMap fun q => (List.range 5).map fun k =>
        Wire.lit (c.xv q (if white then k else k + 5))), w.Bounded s.nv := by
    intro w hw
    rw [List.mem_flatMap] at hw
    obtain ⟨q, hq, hw⟩ := hw
    rw [List.mem_map] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    have hk5 := List.mem_range.mp hk
    exact layout_bounded hs hl q _ hq (by
      cases white with
      | true => show k < 11; omega
      | false => show k + 5 < 11; omega)
  refine triple_bind (atmost_spec s hs .material (by decide) _ 15 hbnd0) ?_
  intro _ s₁ hinv₁ hext₁ hof₁ hQ₁
  refine triple_bind (matKindLoop white s₁ hinv₁ (layout_mono hext₁ hl)) ?_
  intro ex₁ s₂ hinv₂ hext₂ hof₂ hI1
  obtain ⟨hb1, hc1, hinfo1⟩ := hI1
  refine triple_bind
    (matBishLoop white s₂ hinv₂ (layout_mono (ext_trans hext₁ hext₂) hl) ex₁ hb1) ?_
  intro ex₂ s₃ hinv₃ hext₃ hof₃ hI2
  obtain ⟨hb2, hc2, hinfo2⟩ := hI2
  have hbpw : ∀ w ∈ (c.squares.map fun q =>
        Wire.lit (c.xv q (if white then 0 else 0 + 5))), w.Bounded s₃.nv := by
    intro w hw
    rw [List.mem_map] at hw
    obtain ⟨q, hq, rfl⟩ := hw
    exact layout_bounded hinv₃ (layout_mono (ext_trans hext₁ (ext_trans hext₂ hext₃)) hl) q _
      hq (by cases white <;> decide)
  have hbnd3 : ∀ w ∈ (c.squares.map (fun q =>
        Wire.lit (c.xv q (if white then 0 else 0 + 5))) ++ ex₂), w.Bounded s₃.nv := by
    intro w hw
    rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact hbpw w hw
    · exact hb2 w hw
  obtain ⟨hinv₄, hext₃₄, hof₄, hQ₄⟩ := atmost_spec s₃ hinv₃ .material (by decide) _ 8 hbnd3
  refine ⟨hinv₄, hext₃₄, hof₄, ?_⟩
  intro p A hfp hg₄
  intro fc hfc hng
  have hext₁₃ := ext_trans hext₂ hext₃
  have hext₁₄ := ext_trans hext₁₃ hext₃₄
  rw [newCls_trans hext₁ hext₁₄, newCls_trans hext₁₃ hext₃₄, newCls_trans hext₂ hext₃] at hfc
  rcases List.mem_append.mp hfc with hfc | hfc
  · rcases List.mem_cons.mp (hof₁ fc hfc) with hfcase | hfcase
    · exact (hng hfcase).elim
    · have hg₁ := good_mono hext₁₄ hg₄
      have hl₁ := layout_mono hext₁ hl
      have hmen := material_men_count c hfp hg₁ hl₁ white
      have hmle := hfp.1.menLe (colOf white)
      have hcnt0 : ((c.squares.flatMap fun q =>
            (List.range 5).map fun k =>
              Wire.lit (c.xv q (if white then k else k + 5))).filter
            (·.eval A)).length ≤ 15 := by
        omega
      exact (hQ₁ p A hg₁ fc hfc (List.mem_singleton.mp hfcase)).mpr hcnt0
  · rcases List.mem_append.mp hfc with hfc | hfc
    · rcases List.mem_append.mp hfc with hfc | hfc
      · rcases List.mem_cons.mp (hof₂ fc hfc) with hfcase | hfcase
        · exact (hng hfcase).elim
        · exact (hinfo1 fc hfc (List.mem_singleton.mp hfcase)).elim
      · rcases List.mem_cons.mp (hof₃ fc hfc) with hfcase | hfcase
        · exact (hng hfcase).elim
        · exact (hinfo2 fc hfc (List.mem_singleton.mp hfcase)).elim
    · rcases List.mem_cons.mp (hof₄ fc hfc) with hfcase | hfcase
      · exact (hng hfcase).elim
      · have hg₃ := good_mono hext₃₄ hg₄
        have hl₃ := layout_mono (ext_trans hext₁ hext₁₃) hl
        have hNpw := material_lits_count c hfp hg₃ hl₃ white 0 (by decide)
        have hex2 := hc2 p A hfp hg₃
        have hex1 := hc1 p A hfp (good_mono hext₃ hg₃)
        have hmat : (cnt p.board (colOf white) .pawn +
            (cnt p.board (colOf white) .knight - 2) + (cnt p.board (colOf white) .rook - 2) +
            (cnt p.board (colOf white) .queen - 1) + (cntB p.board (colOf white) 0 - 1) +
            (cntB p.board (colOf white) 1 - 1)) ≤ 8 := hfp.1.material (colOf white)
        have hfsum : (([(1, 2), (3, 2), (4, 1)].map fun kb =>
              cnt p.board (colOf white) (kindOf kb.1) - kb.2).sum) =
            cnt p.board (colOf white) .knight - 2 +
              (cnt p.board (colOf white) .rook - 2 +
                (cnt p.board (colOf white) .queen - 1 + 0)) := rfl
        have hgsum : (([0, 1].map fun par => cntB p.board (colOf white) par - 1).sum) =
            cntB p.board (colOf white) 0 - 1 + (cntB p.board (colOf white) 1 - 1 + 0) := rfl
        have hkind0 : cnt p.board (colOf white) (kindOf 0) =
            cnt p.board (colOf white) .pawn := rfl
        have htot : ((c.squares.map (fun q =>
              Wire.lit (c.xv q (if white then 0 else 0 + 5))) ++ ex₂).filter
              (·.eval A)).length ≤ 8 := by
          rw [List.filter_append, List.length_append, hNpw, hex2, hex1, hfsum, hgsum, hkind0]
          omega
        exact (hQ₄ p A hg₄ fc hfc (List.mem_singleton.mp hfcase)).mpr htot

theorem compileCand_spec (s : St) (hs : Inv s) (m : Cand)
    (hb : m.pseudo.Bounded s.nv ∧ m.legal.Bounded s.nv ∧ m.chk.Bounded s.nv)
    (hpl : ∀ A, m.skip = true → m.pseudo.eval A = false → m.legal.eval A = false) :
    Triple (Cfg.compileCand m) s [] fun x s' => x.1 = m ∧ x.2.1.Bounded s'.nv ∧ x.2.2.Bounded s'.nv ∧
      ∀ p A, Good p A s' → x.2.1.eval A = m.legal.eval A ∧ (x.2.1.eval A = true → x.2.2.eval A = m.chk.eval A) := by
  show Triple (compile m.pseudo >>= fun ps =>
      if m.skip && ps == Wire.ff then pure (m, Wire.ff, Wire.ff)
      else (compile m.legal >>= fun lg => (compile m.chk >>= fun ck => pure (m, lg, ck)))) s [] _
  refine triple_bind (compile_spec s hs m.pseudo hb.1) ?_
  intro ps s₁ hinv₁ hext₁ hof₁ hQ₁
  obtain ⟨hpsB, hpsE⟩ := hQ₁
  split
  · next hcond =>
    have hskip : m.skip = true := (Bool.and_eq_true_iff.mp hcond).1
    have hpsff : ps = Wire.ff := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).2
    refine triple_pure (m, Wire.ff, Wire.ff) s₁ hinv₁ [] _ ⟨rfl, trivial, trivial, ?_⟩
    intro p A hg
    refine ⟨?_, fun h => nomatch h⟩
    show false = m.legal.eval A
    have h1 : ps.eval A = false := by rw [hpsff]; rfl
    rw [hpsE p A hg] at h1
    exact (hpl A hskip h1).symm
  · next hcond =>
    refine triple_bind (compile_spec s₁ hinv₁ m.legal (ex_bounded_mono
      (by rw [hs.nv, hinv₁.nv]; exact hext₁.defs_le) hb.2.1)) ?_
    intro lg s₂ hinv₂ hext₂ hof₂ hQ₂
    obtain ⟨hlgB, hlgE⟩ := hQ₂
    refine triple_bind (compile_spec s₂ hinv₂ m.chk (ex_bounded_mono
      (by rw [hs.nv, hinv₂.nv]; exact Nat.le_trans hext₁.defs_le hext₂.defs_le) hb.2.2)) ?_
    intro ck s₃ hinv₃ hext₃ _ hQ₃
    obtain ⟨hckB, hckE⟩ := hQ₃
    refine triple_pure (m, lg, ck) s₃ hinv₃ [] _ ⟨rfl, ?_, hckB, ?_⟩
    · exact wire_bounded_mono (by rw [hinv₂.nv, hinv₃.nv]; exact hext₃.defs_le) hlgB
    · intro p A hg
      exact ⟨hlgE p A (good_mono hext₃ hg), fun _ => hckE p A hg⟩

theorem cands_bounded (hc : CfgOk c) (s : St) (hs : Inv s) (hl : Layout c s) (r : Rights) (hr : RightsOk c s r)
    (hn : 11 * c.squares.length ≤ s.nv) :
    ∀ m ∈ c.cands r, (m.pseudo.Bounded s.nv ∧ m.legal.Bounded s.nv ∧ m.chk.Bounded s.nv) ∧
      ∀ A, m.skip = true → m.pseudo.eval A = false → m.legal.eval A = false := by
  intro m hm
  rcases (mem_cands m).mp hm with ⟨q, hq, hm⟩ | hm | hm
  · rcases hm with hm | hm
    · simp only [Cfg.pieceCands, List.mem_flatMap, List.mem_map] at hm
      obtain ⟨T, hT, t, ht, rfl⟩ := hm
      have hT14 : 1 ≤ T ∧ T ≤ 4 := by
        have : T = 1 ∨ T = 2 ∨ T = 3 ∨ T = 4 := by simpa using hT
        rcases this with rfl | rfl | rfl | rfl <;> decide
      have ht64 : t < 64 := mem_targets_lt ht
      have hq64 : q < 64 := List.mem_range.mp (List.mem_filter.mp hq).1
      have hps : (if T == 1 then Ex.and [c.p q T, Ex.not (c.wocc t)]
          else Ex.and [c.p q T, c.clear q t [] [], Ex.not (c.wocc t)]).Bounded s.nv := by
        split
        · exact ⟨e3_p_bounded hs hl q T hq64 (by omega), e3_wocc_bounded hs hl t ht64, trivial⟩
        · exact ⟨e3_p_bounded hs hl q T hq64 (by omega), e3_clear_bounded hs hl q t [] [],
            e3_wocc_bounded hs hl t ht64, trivial⟩
      obtain ⟨h1, h2, h3, h4⟩ := e3_mkMove_bounded hs hl q t none T _ none 1 hps
      exact ⟨⟨h1, h2, h3⟩, h4⟩
    · obtain ⟨t, pr, ep, ps, w, rfl, ht64, hps⟩ := e3_pawnCands_lform hs hl hr q hq m hm
      obtain ⟨h1, h2, h3, h4⟩ := e3_mkMove_bounded hs hl q t pr 0 ps ep w hps
      exact ⟨⟨h1, h2, h3⟩, h4⟩
  · simp only [Cfg.kingCands, List.mem_filterMap] at hm
    obtain ⟨t, htr, hm⟩ := hm
    have ht64 : t < 64 := List.mem_range.mp htr
    split at hm
    · next hcond =>
      obtain rfl := (Option.some.inj hm).symm
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · exact e3_wocc_bounded hs hl t ht64
      · exact ⟨e3_wocc_bounded hs hl t ht64, e3_attB_bounded hs hl t _ _ _, trivial⟩
      · exact e3_attW_bounded hs hl c.kb [c.kw] [t] [t] t
      · intro A hskip
        exact absurd hskip (by decide : ¬ (false = true))
    · simp at hm
  · simp only [Cfg.castleCands, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · have hlk : r.cr.lookup true = some v := Option.mem_toList.mp hv
      obtain ⟨hv0, hvd⟩ := hr.2.2.1 true v (e3_mem_of_lookup r.cr true v hlk)
      have hvb : (Ex.v v).Bounded s.nv := e3_lit_bounded_of_def hs v hv0 hvd
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · show (Ex.k true).Bounded s.nv; trivial
      · show (Ex.and [Ex.v v, c.empty F1, c.empty G1, Ex.not (c.attB E1 [E1] [] []),
            Ex.not (c.attB F1 [E1] [] []), Ex.not (c.attB G1 [E1, H1] [F1] [])]).Bounded s.nv
        exact ⟨hvb, e3_empty_bounded hs hl F1 (by decide), e3_empty_bounded hs hl G1 (by decide),
          e3_attB_bounded hs hl E1 _ _ _, e3_attB_bounded hs hl F1 _ _ _, e3_attB_bounded hs hl G1 _ _ _,
          trivial⟩
      · show (Ex.or [c.direct F1 3 [E1, H1] [G1], c.attW c.kb [E1, H1] [F1, G1] [F1, G1] G1]).Bounded s.nv
        exact ⟨e3_direct_bounded hs hl F1 3 _ _, e3_attW_bounded hs hl c.kb _ _ _ G1, trivial⟩
      · intro A hskip
        exact absurd hskip (by decide : ¬ (false = true))
    · have hlk : r.cr.lookup false = some v := Option.mem_toList.mp hv
      obtain ⟨hv0, hvd⟩ := hr.2.2.1 false v (e3_mem_of_lookup r.cr false v hlk)
      have hvb : (Ex.v v).Bounded s.nv := e3_lit_bounded_of_def hs v hv0 hvd
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · show (Ex.k true).Bounded s.nv; trivial
      · show (Ex.and [Ex.v v, c.empty B1, c.empty C1, c.empty D1, Ex.not (c.attB E1 [E1] [] []),
            Ex.not (c.attB D1 [E1] [] []), Ex.not (c.attB C1 [E1, A1] [D1] [])]).Bounded s.nv
        exact ⟨hvb, e3_empty_bounded hs hl B1 (by decide), e3_empty_bounded hs hl C1 (by decide),
          e3_empty_bounded hs hl D1 (by decide), e3_attB_bounded hs hl E1 _ _ _,
          e3_attB_bounded hs hl D1 _ _ _, e3_attB_bounded hs hl C1 _ _ _, trivial⟩
      · show (Ex.or [c.direct D1 3 [E1, A1] [C1], c.attW c.kb [E1, A1] [D1, C1] [D1, C1] C1]).Bounded s.nv
        exact ⟨e3_direct_bounded hs hl D1 3 _ _, e3_attW_bounded hs hl c.kb _ _ _ C1, trivial⟩
      · intro A hskip
        exact absurd hskip (by decide : ¬ (false = true))

theorem movesPhase_spec (c : Cfg) (hc : CfgOk c) (s : St) (hs : Inv s) (hl : Layout c s)
    (r : Rights) (hr : RightsOk c s r) (hn : 11 * c.squares.length ≤ s.nv) :
    Triple (c.movesPhase r) s [] fun ms s' => ms.toList.map (·.1) = c.cands r ∧
      (∀ x ∈ ms, x.2.1.Bounded s'.nv) ∧
      ∀ p A, Good p A s' → ∀ x ∈ ms, x.2.1.eval A = x.1.legal.eval A ∧
        (x.2.1.eval A = true → x.2.2.eval A = x.1.chk.eval A) := by
  show Triple ((c.cands r).toArray.mapM Cfg.compileCand) s [] _
  rw [List.mapM_toArray]
  have hrun : ((List.toArray <$> List.mapM Cfg.compileCand (c.cands r)).run s) =
      (((List.mapM Cfg.compileCand (c.cands r)).run s).1.toArray,
       ((List.mapM Cfg.compileCand (c.cands r)).run s).2) := rfl
  obtain ⟨hI, hE, hO, hlen, hBall, hV⟩ := e3_triple_listMapM (c.cands r) Cfg.compileCand s hs
    (fun b n => b.2.1.Bounded n) (fun b n n' hnn hb => wire_bounded_mono hnn hb)
    (fun m b => b.1 = m)
    (fun m b p A => b.2.1.eval A = m.legal.eval A ∧ (b.2.1.eval A = true → b.2.2.eval A = m.chk.eval A))
    (fun m hm s₁ hinv₁ hExt1 => by
      obtain ⟨hbbd, hpl⟩ := cands_bounded c hc s hs hl r hr hn m hm
      have hle : s.nv ≤ s₁.nv := by rw [hs.nv, hinv₁.nv]; exact hExt1.defs_le
      refine triple_mono (compileCand_spec s₁ hinv₁ m
        ⟨ex_bounded_mono hle hbbd.1, ex_bounded_mono hle hbbd.2.1, ex_bounded_mono hle hbbd.2.2⟩ hpl)
        (fun f hf => hf) ?_
      intro x s₂ hinv₂ hext₂ hQcc
      obtain ⟨hx1, hb1, hck, hEv⟩ := hQcc
      exact ⟨hb1, hx1, fun p A hg => hEv p A hg⟩)
  unfold Triple
  rw [hrun]
  refine ⟨hI, hE, hO, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [List.toList_toArray]
    apply List.ext_getElem (by rw [List.length_map]; exact hlen)
    intro i h1 h2
    rw [List.getElem_map]
    rw [List.length_map] at h1
    exact (hV i h2 h1).1
  · intro x hx
    have hx' : x ∈ ((List.mapM Cfg.compileCand (c.cands r)).run s).1 := by
      rw [Array.mem_def, List.toList_toArray] at hx
      exact hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx'
    rw [← hxi]
    exact hBall _ (List.mem_of_getElem rfl)
  · intro p A hg x hx
    have hx' : x ∈ ((List.mapM Cfg.compileCand (c.cands r)).run s).1 := by
      rw [Array.mem_def, List.toList_toArray] at hx
      exact hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx'
    have h2 : i < (c.cands r).length := hlen ▸ hi
    obtain ⟨hV0i, hVi⟩ := hV i h2 hi
    rw [hxi] at hV0i hVi
    rw [← hV0i] at hVi
    exact hVi p A hg

theorem countPhase_spec (thr : Nat) (ms : Array (Cand × Wire × Wire)) (s : St) (hs : Inv s)
    (hb : ∀ x ∈ ms, x.2.1.Bounded s.nv) :
    Triple (countPhase thr true ms) s [.allcheck, .thr] fun _ s' => ∀ p A, Good p A s' →
      (∀ x ∈ ms, x.2.1.eval A = true → x.2.2.eval A = true) →
      thr ≤ ((ms.toList.filter (·.2.1.eval A)).map (·.1.w)).sum →
      NonGateSat A s s' := by
  unfold countPhase
  simp only [← Array.forIn_toList]
  refine triple_bind (triple_mono (e3_countPhase_loop ms s hs)
    (fun f hf => by
      rcases List.mem_cons.mp hf with rfl | hf
      · exact List.mem_cons_self
      · exact (List.not_mem_nil hf).elim)
    (fun a s' _ _ h => h)) ?_
  intro cnt s₁ hinv₁ hext₁ hof₁ hpost
  obtain ⟨hcnt, hcls⟩ := hpost
  have hL : ∀ w ∈ cnt, w.Bounded s₁.nv := by
    intro w hw
    rw [hcnt] at hw
    simp only [List.mem_flatMap, List.mem_filter] at hw
    obtain ⟨x, ⟨hxms, -⟩, hwr⟩ := hw
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hwr
    exact wire_bounded_mono (by rw [hs.nv, hinv₁.nv]; exact hext₁.defs_le)
      (hb x (Array.mem_def.mpr hxms))
  obtain ⟨hinv₂, hext₂, hof₂, hQat⟩ := atleast_spec s₁ hinv₁ .thr (by decide) cnt thr hL
  refine ⟨hinv₂, hext₂, ?_, ?_⟩
  · intro fc hfc
    have h := hof₂ fc hfc
    rcases List.mem_cons.mp (hof₂ fc hfc) with hfam | hfam
    · rw [hfam]; exact List.mem_cons_self
    · rcases List.mem_cons.mp hfam with hfam | hfam
      · rw [hfam]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact (List.not_mem_nil hfam).elim
  · intro p A hgood hall hthr fc hfc hfam
    rw [newCls_trans hext₁ hext₂] at hfc
    rcases List.mem_append.mp hfc with h | h
    · obtain ⟨x, hx, hx1, hx2, hfam1, hsat⟩ := hcls fc h
      rw [hsat A, a6_neg_eval A (hb x (Array.mem_def.mpr hx))]
      cases hl : x.2.1.eval A with
      | false => rfl
      | true => rw [hall x (Array.mem_def.mpr hx) hl]; rfl
    · have hfamthr : fc.1 = .thr := by
        have h2 := hof₂ fc h
        rcases List.mem_cons.mp h2 with hf2 | hf2
        · exact absurd hf2 hfam
        · rcases List.mem_cons.mp hf2 with hf2 | hf2
          · exact hf2
          · exact (List.not_mem_nil hf2).elim
      have hlen : (cnt.filter (·.eval A)).length =
          ((ms.toList.filter fun x => x.2.1.eval A).map (·.1.w)).sum := by
        rw [hcnt]
        exact e3_countPhase_cnt_len _ _
      exact (hQat p A hgood fc h hfamthr).mpr (hlen ▸ hthr)

end Phases

theorem defs_lookup_mono {s s' : St} (h : Ext s s') {i : Nat} {d : VDef}
    (hi : s.defs[i]? = some d) : s'.defs[i]? = some d := by
  obtain ⟨hlt, hval⟩ := Array.getElem?_eq_some_iff.mp hi
  exact (h.defs_eq i hlt).trans (congrArg some hval)

theorem layout_ext {c : Cfg} {s s' : St} (h : Ext s s') (hl : Layout c s) : Layout c s' :=
  fun q hq k hk => ⟨(hl q hq k hk).1, defs_lookup_mono h (hl q hq k hk).2⟩

theorem rightsOk_ext {c : Cfg} {s s' : St} {r : Rights} (h : Ext s s') (hr : RightsOk c s r) :
    RightsOk c s' r := by
  obtain ⟨he1, he2, hc1, hc2⟩ := hr
  refine ⟨fun f v hv => ?_, he2, fun b v hv => ?_, hc2⟩
  · obtain ⟨a, b, d⟩ := he1 f v hv
    exact ⟨a, b, defs_lookup_mono h d⟩
  · obtain ⟨a, d⟩ := hc1 b v hv
    exact ⟨a, defs_lookup_mono h d⟩

theorem nonGateSat_trans {A : Assignment} {s₁ s₂ s₃ : St} (e12 : Ext s₁ s₂) (e23 : Ext s₂ s₃)
    (h12 : NonGateSat A s₁ s₂) (h23 : NonGateSat A s₂ s₃) : NonGateSat A s₁ s₃ := by
  intro fc hfc hfam
  rw [newCls_trans e12 e23, List.mem_append] at hfc
  rcases hfc with h | h
  · exact h12 fc h hfam
  · exact h23 fc h hfam

theorem nonGateSat_gate {A : Assignment} {s s' : St} (h : OnlyFams [.gate] s s') :
    NonGateSat A s s' := by
  intro fc hfc hfam
  rcases List.mem_cons.mp (h fc hfc) with h1 | h1
  · exact absurd h1 hfam
  · exact (List.not_mem_nil h1).elim

theorem e4_nv_le {s s' : St} (hs : Inv s) (hs' : Inv s') (h : Ext s s') : s.nv ≤ s'.nv := by
  rw [hs.nv, hs'.nv]
  exact h.defs_le

theorem e4_wsum {A : Assignment} (l : List (Cand × Wire × Wire))
    (h : ∀ x ∈ l, x.2.1.eval A = x.1.legal.eval A) :
    ((l.filter fun x => x.2.1.eval A).map fun x => x.1.w).sum =
      (((l.map fun x => x.1).filter fun m => m.legal.eval A).map fun m => m.w).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := h x List.mem_cons_self
    have ht := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    cases hev : x.2.1.eval A with
    | false =>
      rw [List.filter_cons_of_neg (fun h1 => by
          have h2 : x.2.1.eval A = true := h1
          rw [hev] at h2
          exact Bool.noConfusion h2),
        List.map_cons,
        List.filter_cons_of_neg (fun h1 => by
          have h2 : x.1.legal.eval A = true := h1
          rw [← hx, hev] at h2
          exact Bool.noConfusion h2)]
      exact ht
    | true =>
      rw [List.filter_cons_of_pos (by exact hev), List.map_cons, List.sum_cons, List.map_cons,
        List.filter_cons_of_pos (by
          have h1 : x.1.legal.eval A = true := by rw [← hx, hev]
          exact h1),
        List.map_cons, List.sum_cons, ht]

theorem build_spec {c : Cfg} (hc : CfgOk c) :
    Triple (c.build 64) {} [.onehot, .rank, .start, .ep, .castle, .material, .allcheck, .thr] fun _ s' =>
      ∀ p A, Fits c p → Good p A s' → AllCheck p → 64 ≤ (legalMoves p).length → NonGateSat A {} s' := by
  have r1 := initPhase_spec c hc
  have t1 : Triple c.initPhase {} [.onehot, .rank, .start, .ep, .castle, .material, .allcheck, .thr]
      (fun _ s' => Layout c s' ∧ s'.nv = 11 * c.squares.length ∧
        ∀ p A, Fits c p → Good p A s' → NonGateSat A {} s') := by
    refine ⟨r1.1, r1.2.1, ?_, r1.2.2.2⟩
    intro fc hfc
    have h := r1.2.2.1 fc hfc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h <;> rw [h] <;> decide
  refine triple_bind t1 ?_
  intro _ s1 hi1 hext1 _hof1 hq1
  obtain ⟨hl1, hnv1, hP1⟩ := hq1
  have r2 := startPhase_spec c hc s1 hi1 hl1
  have t2 : Triple c.startPhase s1 [.onehot, .rank, .start, .ep, .castle, .material, .allcheck, .thr]
      (fun _ s' => (∀ p A, Fits c p → Good p A s' → NonGateSat A {} s') ∧ Layout c s' ∧
        11 * c.squares.length ≤ s'.nv ∧ Ext {} s') := by
    refine ⟨r2.1, r2.2.1, ?_, ?_⟩
    · intro fc hfc
      have h := r2.2.2.1 fc hfc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> rw [h] <;> decide
    · exact ⟨fun p A hf hg =>
          nonGateSat_trans hext1 r2.2.1 (hP1 p A hf (good_mono r2.2.1 hg)) (r2.2.2.2 p A hf hg),
        layout_ext r2.2.1 hl1, Nat.le_trans (Nat.le_of_eq hnv1.symm) (e4_nv_le hi1 r2.1 r2.2.1),
        ext_trans hext1 r2.2.1⟩
  refine triple_bind t2 ?_
  intro _ s2 hi2 _hext2 _hof2 hq2
  obtain ⟨hN2, hl2, hnv2, hec2⟩ := hq2
  have r3 := epPhase_spec c hc s2 hi2 hl2
  have t3 : Triple c.epPhase s2 [.onehot, .rank, .start, .ep, .castle, .material, .allcheck, .thr]
      (fun ep s' => ((∀ f v, (f, v) ∈ ep → f < 8 ∧ 0 < v ∧ s'.defs[v.toNat - 1]? = some (.ep f)) ∧
          (∀ f < 8, (ep.lookup f).isSome = !(c.isK (f + 32) || c.isK (f + 40) || c.isK (f + 48)))) ∧
        (∀ p A, Fits c p → Good p A s' → NonGateSat A {} s') ∧ Layout c s' ∧
          11 * c.squares.length ≤ s'.nv ∧ Ext {} s') := by
    refine ⟨r3.1, r3.2.1, ?_, ?_⟩
    · intro fc hfc
      have h := r3.2.2.1 fc hfc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> rw [h] <;> decide
    · exact ⟨⟨r3.2.2.2.1, r3.2.2.2.2.1⟩,
        fun p A hf hg =>
          nonGateSat_trans hec2 r3.2.1 (hN2 p A hf (good_mono r3.2.1 hg)) (r3.2.2.2.2.2 p A hf hg),
        layout_ext r3.2.1 hl2, Nat.le_trans hnv2 (e4_nv_le hi2 r3.1 r3.2.1), ext_trans hec2 r3.2.1⟩
  refine triple_bind t3 ?_
  intro epv s3 hi3 _hext3 _hof3 hq3
  obtain ⟨⟨hed1, hed2⟩, hN3, hl3, hnv3, hec3⟩ := hq3
  have r4 := crPhase_spec c hc s3 hi3 hl3
  have t4 : Triple c.crPhase s3 [.onehot, .rank, .start, .ep, .castle, .material, .allcheck, .thr]
      (fun cr s' => (∀ p A, Fits c p → Good p A s' → NonGateSat A {} s') ∧ Layout c s' ∧
        11 * c.squares.length ≤ s'.nv ∧ RightsOk c s' ⟨epv, cr⟩ ∧ Ext {} s') := by
    refine ⟨r4.1, r4.2.1, ?_, ?_⟩
    · intro fc hfc
      have h := r4.2.2.1 fc hfc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> rw [h] <;> decide
    · exact ⟨fun p A hf hg =>
          nonGateSat_trans hec3 r4.2.1 (hN3 p A hf (good_mono r4.2.1 hg)) (r4.2.2.2.2.2 p A hf hg),
        layout_ext r4.2.1 hl3, Nat.le_trans hnv3 (e4_nv_le hi3 r4.1 r4.2.1),
        ⟨fun f v hv => let ⟨a, b, d⟩ := hed1 f v hv; ⟨a, b, defs_lookup_mono r4.2.1 d⟩, hed2,
          r4.2.2.2.1, r4.2.2.2.2.1⟩,
        ext_trans hec3 r4.2.1⟩
  refine triple_bind t4 ?_
  intro crv s4 hi4 _hext4 _hof4 hq4
  obtain ⟨hN4, hl4, hnv4, hro4, hec4⟩ := hq4
  have r5 := materialPhase_spec c hc true s4 hi4 hl4
  have t5 : Triple (c.materialPhase true) s4 [.onehot, .rank, .start, .ep, .castle, .material,
        .allcheck, .thr]
      (fun _ s' => (∀ p A, Fits c p → Good p A s' → NonGateSat A {} s') ∧ Layout c s' ∧
        11 * c.squares.length ≤ s'.nv ∧ RightsOk c s' ⟨epv, crv⟩ ∧ Ext {} s') := by
    refine ⟨r5.1, r5.2.1, ?_, ?_⟩
    · intro fc hfc
      have h := r5.2.2.1 fc hfc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> rw [h] <;> decide
    · exact ⟨fun p A hf hg =>
          nonGateSat_trans hec4 r5.2.1 (hN4 p A hf (good_mono r5.2.1 hg)) (r5.2.2.2 p A hf hg),
        layout_ext r5.2.1 hl4, Nat.le_trans hnv4 (e4_nv_le hi4 r5.1 r5.2.1),
        rightsOk_ext r5.2.1 hro4, ext_trans hec4 r5.2.1⟩
  refine triple_bind t5 ?_
  intro _ s5 hi5 _hext5 _hof5 hq5
  obtain ⟨hN5, hl5, hnv5, hro5, hec5⟩ := hq5
  have r6 := materialPhase_spec c hc false s5 hi5 hl5
  have t6 : Triple (c.materialPhase false) s5 [.onehot, .rank, .start, .ep, .castle, .material,
        .allcheck, .thr]
      (fun _ s' => (∀ p A, Fits c p → Good p A s' → NonGateSat A {} s') ∧ Layout c s' ∧
        11 * c.squares.length ≤ s'.nv ∧ RightsOk c s' ⟨epv, crv⟩ ∧ Ext {} s') := by
    refine ⟨r6.1, r6.2.1, ?_, ?_⟩
    · intro fc hfc
      have h := r6.2.2.1 fc hfc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> rw [h] <;> decide
    · exact ⟨fun p A hf hg =>
          nonGateSat_trans hec5 r6.2.1 (hN5 p A hf (good_mono r6.2.1 hg)) (r6.2.2.2 p A hf hg),
        layout_ext r6.2.1 hl5, Nat.le_trans hnv5 (e4_nv_le hi5 r6.1 r6.2.1),
        rightsOk_ext r6.2.1 hro5, ext_trans hec5 r6.2.1⟩
  refine triple_bind t6 ?_
  intro _ s6 hi6 _hext6 _hof6 hq6
  obtain ⟨hN6, hl6, hnv6, hro6, hec6⟩ := hq6
  have r7 := movesPhase_spec c hc s6 hi6 hl6 ⟨epv, crv⟩ hro6 hnv6
  have t7 : Triple (c.movesPhase ⟨epv, crv⟩) s6 [.onehot, .rank, .start, .ep, .castle, .material,
        .allcheck, .thr]
      (fun ms s' => (ms.toList.map (·.1) = c.cands ⟨epv, crv⟩ ∧
          (∀ x ∈ ms, x.2.1.Bounded s'.nv) ∧
          ∀ p A, Good p A s' → ∀ x ∈ ms, x.2.1.eval A = x.1.legal.eval A ∧
            (x.2.1.eval A = true → x.2.2.eval A = x.1.chk.eval A)) ∧
        (∀ p A, Fits c p → Good p A s' → NonGateSat A {} s') ∧ Layout c s' ∧
          11 * c.squares.length ≤ s'.nv ∧ RightsOk c s' ⟨epv, crv⟩ ∧ Ext {} s') := by
    refine ⟨r7.1, r7.2.1, ?_, ?_⟩
    · intro fc hfc
      have h := r7.2.2.1 fc hfc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rw [h]
      decide
    · exact ⟨r7.2.2.2,
        fun p A hf hg =>
          nonGateSat_trans hec6 r7.2.1 (hN6 p A hf (good_mono r7.2.1 hg)) (nonGateSat_gate r7.2.2.1),
        layout_ext r7.2.1 hl6, Nat.le_trans hnv6 (e4_nv_le hi6 r7.1 r7.2.1),
        rightsOk_ext r7.2.1 hro6, ext_trans hec6 r7.2.1⟩
  refine triple_bind t7 ?_
  intro msv s7 hi7 _hext7 _hof7 hq7
  obtain ⟨⟨hmap, hbnd, heval⟩, hN7, hl7, hnv7, hro7, hec7⟩ := hq7
  have r8 := countPhase_spec 64 msv s7 hi7 hbnd
  have t8 : Triple (countPhase 64 true msv) s7 [.onehot, .rank, .start, .ep, .castle, .material,
        .allcheck, .thr]
      (fun _ s' => ∀ p A, Fits c p → Good p A s' → AllCheck p → 64 ≤ (legalMoves p).length →
        NonGateSat A {} s') := by
    refine ⟨r8.1, r8.2.1, ?_, ?_⟩
    · intro fc hfc
      have h := r8.2.2.1 fc hfc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> rw [h] <;> decide
    · intro p A hf hg hall h64
      have hg7 : Good p A s7 := good_mono r8.2.1 hg
      have hcond1 : ∀ x ∈ msv, x.2.1.eval A = true → x.2.2.eval A = true := by
        intro x hx ht
        obtain ⟨ev1, ev2⟩ := heval p A hg7 x hx
        have hxm : x.1 ∈ c.cands ⟨epv, crv⟩ := by
          rw [← hmap]
          exact List.mem_map.mpr ⟨x, Array.mem_def.mp hx, rfl⟩
        have hlg : x.1.legal.eval A = true := by rw [← ev1]; exact ht
        have hmv := cand_legal hf hg7 hl7 hro7 x.1 hxm hlg
        rw [ev2 ht, cand_chk hf hg7 hl7 hro7 x.1 hxm hlg]
        exact hall _ hmv
      have hcond2 : 64 ≤ ((msv.toList.filter (·.2.1.eval A)).map (·.1.w)).sum := by
        have h1 : 64 ≤ (((c.cands ⟨epv, crv⟩).filter (·.legal.eval A)).map (·.w)).sum :=
          Nat.le_trans h64 (count_le hf hg7 hl7 hro7)
        rw [← hmap] at h1
        rw [← e4_wsum msv.toList fun x hx => (heval p A hg7 x (Array.mem_def.mpr hx)).1] at h1
        exact h1
      exact nonGateSat_trans hec7 r8.2.1 (hN7 p A hf hg7) (r8.2.2.2 p A hg hcond1 hcond2)
  refine triple_bind t8 ?_
  intro _ s8 hi8 _hext8 _hof8 hN8
  exact triple_pure _ s8 hi8 _ _ hN8

theorem encode_sat {c : Cfg} {p : Pos} (hf : Fits c p) (hall : AllCheck p) (h64 : 64 ≤ (legalMoves p).length) :
    (G c).Sat (assign p (c.encode 64)) := by
  have key := build_spec (fits_cfgOk hf)
  unfold Triple at key
  have hG : G c = ((c.build 64).run {}).2.toCnf := rfl
  have hE : c.encode 64 = ((c.build 64).run {}).2 := rfl
  rw [hG, hE]
  generalize ((c.build 64).run {}) = S at key ⊢
  obtain ⟨hs, -, -, hq⟩ := key
  have hg := good_assign p S.2 hs
  intro cl hcl
  simp only [St.toCnf, Array.mem_map] at hcl
  obtain ⟨fc, hfc, rfl⟩ := hcl
  by_cases hgate : fc.1 = .gate
  · exact gate_cls_sat hs hg fc hfc hgate
  · exact hq p _ hf hg hall h64 fc (by simpa [NewCls] using hfc) hgate

end Chess.All63
