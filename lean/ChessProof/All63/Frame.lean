import ChessProof.All63.Circuit
import ChessProof.All63.Assign

namespace Chess.All63

def Wire.Bounded (n : Nat) : Wire → Prop
  | .lit l => 0 < l.natAbs ∧ l.natAbs ≤ n
  | _ => True

mutual
def Ex.Bounded (n : Nat) : Ex → Prop
  | .k _ => True
  | .v l => 0 < l.natAbs ∧ l.natAbs ≤ n
  | .not e => e.Bounded n
  | .and es => Ex.BoundedAll n es
  | .or es => Ex.BoundedAll n es

def Ex.BoundedAll (n : Nat) : List Ex → Prop
  | [] => True
  | e :: es => e.Bounded n ∧ Ex.BoundedAll n es
end

def tseitin (g : Nat) (isAnd : Bool) (L : List Int) : List Clause :=
  if isAnd then L.map (fun l => #[-(g : Int), l]) ++ [#[(g : Int)] ++ (L.map (- ·)).toArray]
  else L.map (fun l => #[(g : Int), -l]) ++ [#[-(g : Int)] ++ L.toArray]

structure Inv (s : St) : Prop where
  nv : s.nv = s.defs.size
  cache : ∀ b L g, s.cache[(b, L)]? = some g → 0 < g ∧ g ≤ s.nv ∧ s.defs[g - 1]? = some (.gate b L)
  wf : ∀ i (h : i < s.defs.size) b L, s.defs[i] = .gate b L → ∀ l ∈ L, 0 < l.natAbs ∧ l.natAbs ≤ i
  gates : ∀ fc ∈ s.cls, fc.1 = .gate →
    ∃ i, ∃ h : i < s.defs.size, ∃ b L, s.defs[i] = .gate b L ∧ fc.2 ∈ tseitin (i + 1) b L

structure Ext (s s' : St) : Prop where
  defs_le : s.defs.size ≤ s'.defs.size
  defs_eq : ∀ i (h : i < s.defs.size), s'.defs[i]? = some s.defs[i]
  cls_prefix : ∃ new, s'.cls = s.cls ++ new

def NewCls (s s' : St) : List (Fam × Clause) := s'.cls.toList.drop s.cls.size

def OnlyFams (fs : List Fam) (s s' : St) : Prop := ∀ fc ∈ NewCls s s', fc.1 ∈ fs

def Triple (x : M α) (s : St) (fs : List Fam) (Q : α → St → Prop) : Prop :=
  Inv (x.run s).2 ∧ Ext s (x.run s).2 ∧ OnlyFams (.gate :: fs) s (x.run s).2 ∧ Q (x.run s).1 (x.run s).2

theorem ext_refl (s : St) : Ext s s := ⟨Nat.le_refl _, fun i h => by simp [h], ⟨#[], by simp⟩⟩

theorem ext_trans {s₁ s₂ s₃ : St} (h₁ : Ext s₁ s₂) (h₂ : Ext s₂ s₃) : Ext s₁ s₃ := by
  obtain ⟨a1, b1, n1, e1⟩ := h₁
  obtain ⟨a2, b2, n2, e2⟩ := h₂
  refine ⟨Nat.le_trans a1 a2, fun i h => ?_, ⟨n1 ++ n2, by simp [e1, e2]⟩⟩
  have := b1 i h
  have hi : i < s₂.defs.size := by omega
  rw [b2 i hi]
  simp [Array.getElem?_eq_getElem hi] at this ⊢
  exact this

theorem drop_append_trans {α : Type} (a b c : List α) :
    (a ++ (b ++ c)).drop a.length = (a ++ b).drop a.length ++ (a ++ (b ++ c)).drop (a.length + b.length) := by
  rw [List.drop_left, List.drop_left, ← List.drop_drop, List.drop_left, List.drop_left]

theorem newCls_trans {s₁ s₂ s₃ : St} (h₁ : Ext s₁ s₂) (h₂ : Ext s₂ s₃) :
    NewCls s₁ s₃ = NewCls s₁ s₂ ++ NewCls s₂ s₃ := by
  obtain ⟨n₁, he₁⟩ := h₁.cls_prefix
  obtain ⟨n₂, he₂⟩ := h₂.cls_prefix
  have e := drop_append_trans s₁.cls.toList n₁.toList n₂.toList
  simp only [NewCls, he₁, he₂, Array.toList_append, Array.size_append, List.append_assoc]
  exact e

theorem newCls_self (s : St) : NewCls s s = [] := by
  simp [NewCls, ← Array.length_toList]

theorem triple_pure {α : Type} (a : α) (s : St) (hs : Inv s) (fs : List Fam) (Q : α → St → Prop) (hq : Q a s) :
    Triple (pure a : M α) s fs Q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hs
  · exact ext_refl s
  · intro fc hfc
    have h : fc ∈ NewCls s s := hfc
    rw [newCls_self] at h
    exact (List.not_mem_nil h).elim
  · exact hq

theorem triple_bind {α β : Type} {x : M α} {f : α → M β} {s : St} {fs : List Fam} {Q : α → St → Prop}
    {R : β → St → Prop} (hx : Triple x s fs Q)
    (hf : ∀ a s', Inv s' → Ext s s' → OnlyFams (.gate :: fs) s s' → Q a s' → Triple (f a) s' fs R) :
    Triple (x >>= f) s fs R := by
  obtain ⟨hinv1, hext1, hof1, hq1⟩ := hx
  obtain ⟨hinv2, hext2, hof2, hq2⟩ := hf (x.run s).1 (x.run s).2 hinv1 hext1 hof1 hq1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hinv2
  · exact ext_trans hext1 hext2
  · intro fc hfc
    have h : fc ∈ NewCls s ((f (x.run s).1).run (x.run s).2).2 := hfc
    rw [newCls_trans hext1 hext2] at h
    rcases List.mem_append.mp h with h | h
    · exact hof1 fc h
    · exact hof2 fc h
  · exact hq2

theorem triple_mono {α : Type} {x : M α} {s : St} {fs fs' : List Fam} {Q Q' : α → St → Prop}
    (hx : Triple x s fs Q) (hfs : ∀ f ∈ fs, f ∈ fs') (hq : ∀ a s', Inv s' → Ext s s' → Q a s' → Q' a s') :
    Triple x s fs' Q' := by
  obtain ⟨hinv, hext, hof, hqx⟩ := hx
  refine ⟨hinv, hext, fun fc hfc => ?_, hq _ _ hinv hext hqx⟩
  have h := hof fc hfc
  simp only [List.mem_cons] at h ⊢
  rcases h with h | h
  · exact .inl h
  · exact .inr (hfs _ h)

theorem triple_forIn {α β : Type} (l : List α) (b : β) (body : α → β → M (ForInStep β)) (s : St) (fs : List Fam)
    (I : List α → β → St → Prop) (hs : Inv s) (h0 : I [] b s)
    (hstep : ∀ pre a rest b' s', l = pre ++ a :: rest → Inv s' → Ext s s' → OnlyFams (.gate :: fs) s s' →
      I pre b' s' → Triple (body a b') s' fs fun r s'' => match r with
        | .done b'' => I l b'' s''
        | .yield b'' => I (pre ++ [a]) b'' s'') :
    Triple (forIn l b body) s fs fun b' s' => I l b' s' := by
  have onlyFams_self : OnlyFams (.gate :: fs) s s := fun fc hfc => by
    rw [newCls_self] at hfc
    exact (List.not_mem_nil hfc).elim
  suffices H : ∀ rest pre b s', l = pre ++ rest → Inv s' → Ext s s' → OnlyFams (.gate :: fs) s s' →
      I pre b s' → Triple (forIn rest b body) s' fs fun b' s' => I l b' s' by
    exact H l [] b s (by simp) hs (ext_refl s) onlyFams_self h0
  intro rest
  induction rest with
  | nil =>
    intro pre b s' hl hinv hext hof hI
    rw [List.append_nil] at hl
    subst hl
    rw [List.forIn_nil]
    exact triple_pure b s' hinv fs _ hI
  | cons a rest ih =>
    intro pre b s' hl hinv hext hof hI
    rw [List.forIn_cons]
    refine triple_bind (hstep pre a rest b s' hl hinv hext hof hI) ?_
    intro r s'' hinv' hext' hof' hQ
    have hof'' : OnlyFams (.gate :: fs) s s'' := fun fc hfc => by
      rw [newCls_trans hext hext'] at hfc
      rcases List.mem_append.mp hfc with hfc | hfc
      · exact hof fc hfc
      · exact hof' fc hfc
    cases r with
    | done b'' => exact triple_pure b'' s'' hinv' fs _ hQ
    | yield b'' =>
      exact ih (pre ++ [a]) b'' s'' (by rw [hl, List.append_cons]) hinv' (ext_trans hext hext') hof'' hQ

theorem inv_empty : Inv ({} : St) := by
  refine ⟨rfl, fun b L g h => ?_, fun i h => absurd h (Nat.not_lt_zero i),
    fun fc hfc _ => (Array.not_mem_empty fc hfc).elim⟩
  rw [show ({} : St).cache = (∅ : Std.HashMap (Bool × List Int) Nat) from rfl,
    Std.HashMap.getElem?_empty] at h
  nomatch h

theorem wire_bounded_mono {n n' : Nat} {w : Wire} (h : n ≤ n') (hw : w.Bounded n) : w.Bounded n' := by
  cases w <;> simp_all [Wire.Bounded] <;> omega

mutual
theorem ex_bounded_mono_aux {n n' : Nat} {e : Ex} (h : n ≤ n') (he : e.Bounded n) : e.Bounded n' := by
  cases e with
  | k b => trivial
  | v l => obtain ⟨h1, h2⟩ := he; exact ⟨h1, Nat.le_trans h2 h⟩
  | not e => exact ex_bounded_mono_aux (e := e) h he
  | and es => exact ex_boundedAll_mono_aux (es := es) h he
  | or es => exact ex_boundedAll_mono_aux (es := es) h he
termination_by sizeOf e
decreasing_by all_goals (try subst_vars; simp_all; try omega)

theorem ex_boundedAll_mono_aux {n n' : Nat} {es : List Ex} (h : n ≤ n') (he : Ex.BoundedAll n es) :
    Ex.BoundedAll n' es := by
  cases es with
  | nil => trivial
  | cons e es => exact ⟨ex_bounded_mono_aux (e := e) h he.1, ex_boundedAll_mono_aux (es := es) h he.2⟩
termination_by sizeOf es
decreasing_by all_goals (try subst_vars; simp_all; try omega)
end

theorem ex_bounded_mono {n n' : Nat} {e : Ex} (h : n ≤ n') (he : e.Bounded n) : e.Bounded n' :=
  ex_bounded_mono_aux h he

theorem good_mono {p : Pos} {A : Assignment} {s s' : St} (h : Ext s s') (hg : Good p A s') : Good p A s := by
  intro i hi
  have hi' : i < s'.defs.size := Nat.lt_of_lt_of_le hi h.defs_le
  have hge := h.defs_eq i hi
  rw [Array.getElem?_eq_getElem hi'] at hge
  exact (Option.some.inj hge) ▸ hg i hi'

def valsPush (p : Pos) (acc : Array Bool) (d : VDef) : Array Bool :=
  acc.push (d.val p fun v => if v = 0 then false else acc.getD (v - 1) false)

theorem list_all_mem_congr {L : List Int} {p q : Int → Bool} (h : ∀ a ∈ L, p a = q a) :
    L.all p = L.all q := by
  induction L with
  | nil => rfl
  | cons a t ih =>
      rw [List.all_cons, List.all_cons, h a (List.mem_cons_self : a ∈ a :: t),
        ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem list_any_mem_congr {L : List Int} {p q : Int → Bool} (h : ∀ a ∈ L, p a = q a) :
    L.any p = L.any q := by
  induction L with
  | nil => rfl
  | cons a t ih =>
      rw [List.any_cons, List.any_cons, h a (List.mem_cons_self : a ∈ a :: t),
        ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem litVal_congr {A₁ A₂ : Assignment} {l : Int} {n : Nat}
    (h1 : 0 < l.natAbs) (h2 : l.natAbs ≤ n) (h : ∀ v, 1 ≤ v → v ≤ n → A₁ v = A₂ v) :
    litVal A₁ l = litVal A₂ l := by
  have hh := h l.natAbs h1 h2
  unfold litVal
  by_cases hp : 0 < l
  · have e : l.toNat = l.natAbs := by omega
    rw [if_pos hp, if_pos hp, e, hh]
  · rw [if_neg hp, if_neg hp, hh]

theorem vdef_val_congr {p : Pos} {d : VDef} {n : Nat} {A₁ A₂ : Assignment}
    (hwf : ∀ b L, d = .gate b L → ∀ l ∈ L, 0 < l.natAbs ∧ l.natAbs ≤ n)
    (h : ∀ v, 1 ≤ v → v ≤ n → A₁ v = A₂ v) : d.val p A₁ = d.val p A₂ := by
  cases d with
  | x q k => rfl
  | ep f => rfl
  | cr ks => rfl
  | gate b L =>
      have hl : ∀ l ∈ L, litVal A₁ l = litVal A₂ l := fun l hm =>
        litVal_congr (hwf b L rfl l hm).1 (hwf b L rfl l hm).2 h
      cases b with
      | true => exact list_all_mem_congr hl
      | false => exact list_any_mem_congr hl

theorem getD_push_lt (a : Array Bool) (x : Bool) {j : Nat} (h : j < a.size) :
    (a.push x).getD j false = a.getD j false := by
  have h' : j < (a.push x).size := by rw [Array.size_push]; omega
  show (if h : j < (a.push x).size then (a.push x).getInternal j h else false) =
    (if h : j < a.size then a.getInternal j h else false)
  rw [dif_pos h', dif_pos h, Array.getInternal_eq_getElem, Array.getInternal_eq_getElem]
  exact Array.getElem_push_lt h

theorem getD_push_self (a : Array Bool) (x : Bool) : (a.push x).getD a.size false = x := by
  have h : a.size < (a.push x).size := by rw [Array.size_push]; omega
  show (if h : a.size < (a.push x).size then (a.push x).getInternal a.size h else false) = x
  rw [dif_pos h, Array.getInternal_eq_getElem]
  exact Array.getElem_push_eq

theorem valsOf_val (p : Pos) (defs : Array VDef)
    (hwf : ∀ i (h : i < defs.size) b L, defs[i] = .gate b L → ∀ l ∈ L, 0 < l.natAbs ∧ l.natAbs ≤ i)
    {j : Nat} (hj : j < defs.size) :
    (valsOf p defs).getD j false =
      defs[j].val p fun v => if v = 0 then false else (valsOf p defs).getD (v - 1) false := by
  rw [show valsOf p defs = defs.foldl (valsPush p) #[] from rfl]
  have hind : (defs.foldl (valsPush p) #[]).size = defs.size ∧
      ∀ j (hjj : j < defs.size) (hjd : j < defs.size), (defs.foldl (valsPush p) #[]).getD j false =
        (defs[j]'hjd).val p fun v => if v = 0 then false else
          (defs.foldl (valsPush p) #[]).getD (v - 1) false := by
    refine Array.foldl_induction (α := VDef) (β := Array Bool) (as := defs) (init := #[])
      (motive := fun i acc => acc.size = i ∧
        ∀ j (hjj : j < i) (hjd : j < defs.size), acc.getD j false =
          (defs[j]'hjd).val p fun v => if v = 0 then false else acc.getD (v - 1) false)
      ⟨rfl, fun j hjj hjd => absurd hjj (Nat.not_lt_zero j)⟩ ?_
    intro i b hbi
    obtain ⟨hsize, hval⟩ := hbi
    refine ⟨by show (b.push _).size = ↑i + 1; rw [Array.size_push, hsize], fun j hjj hjd => ?_⟩
    show (b.push (defs[i].val p fun v => if v = 0 then false else b.getD (v - 1) false)).getD j false = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjj with hlt | heq
    · refine (getD_push_lt b _ (by rw [hsize]; exact hlt)).trans ?_
      rw [hval j hlt hjd]
      refine vdef_val_congr (fun b' L hd => hwf j hjd b' L hd) ?_
      intro v hv1 hvj
      show (if v = 0 then false else b.getD (v - 1) false) =
        (if v = 0 then false else
          (b.push (defs[i].val p fun v => if v = 0 then false else b.getD (v - 1) false)).getD (v - 1) false)
      rw [if_neg (by omega), if_neg (by omega), getD_push_lt b _ (by rw [hsize]; omega)]
    · subst heq
      have e1 : (b.push (defs[i].val p fun v => if v = 0 then false else b.getD (v - 1) false)).getD ↑i false =
          defs[i].val p fun v => if v = 0 then false else b.getD (v - 1) false := by
        have e := getD_push_self b (defs[i].val p fun v => if v = 0 then false else b.getD (v - 1) false)
        rwa [hsize] at e
      rw [e1]
      refine vdef_val_congr (fun b' L hd => hwf _ hjd b' L hd) ?_
      intro v hv1 hvi
      show (if v = 0 then false else b.getD (v - 1) false) =
        (if v = 0 then false else
          (b.push (defs[i].val p fun v => if v = 0 then false else b.getD (v - 1) false)).getD (v - 1) false)
      rw [if_neg (by omega), if_neg (by omega), getD_push_lt b _ (by rw [hsize]; omega)]
  exact hind.2 j hj hj

theorem good_assign (p : Pos) (s : St) (hs : Inv s) : Good p (assign p s) s := by
  intro i h
  have e1 : assign p s (i + 1) = (valsOf p s.defs).getD i false := by
    show (if i + 1 = 0 then false else (valsOf p s.defs).getD (i + 1 - 1) false) = _
    rw [if_neg (by omega), Nat.add_sub_cancel]
  exact e1.trans (valsOf_val p s.defs hs.wf h)

theorem clause_sat_of_mem {A : Assignment} {c : Clause} {l : Int} (hm : l ∈ c.toList)
    (hv : litVal A l = true) : c.sat A = true := by
  rw [Clause.sat, Array.any_eq_true]
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
  exact ⟨i, by rw [← Array.length_toList]; exact hi, by rw [← Array.getElem_toList]; exact hv⟩

theorem litVal_neg {A : Assignment} {l : Int} (h : l ≠ 0) : litVal A (-l) = !litVal A l := by
  rw [litVal, litVal]
  by_cases hp : 0 < l
  · have hn : ¬ 0 < -l := by omega
    rw [if_pos hp, if_neg hn]
    have h1 : (-l).natAbs = l.toNat := by omega
    rw [h1]
  · have hn : 0 < -l := by omega
    rw [if_neg hp, if_pos hn]
    have h1 : (-l).toNat = l.natAbs := by omega
    rw [h1]
    rw [Bool.not_not]

theorem tseitin_sat (A : Assignment) (g : Nat) (b : Bool) (L : List Int)
    (hL : ∀ l ∈ L, l ≠ 0)
    (hg : A g = if b then L.all (litVal A) else L.any (litVal A)) (hpos : 0 < g) :
    ∀ cl ∈ tseitin g b L, cl.sat A = true := by
  have hgp : litVal A (g : Int) = A g := by
    rw [litVal, if_pos (Int.natCast_pos.mpr hpos), Int.toNat_natCast]
  have hgn : litVal A (-(g : Int)) = !A g := by
    rw [litVal, if_neg (by omega : ¬ 0 < -(g : Int))]
    have habs : (-(g : Int)).natAbs = g := by omega
    rw [habs]
  have hneg : ∀ l ∈ L, litVal A (-l) = !litVal A l := fun l hl => litVal_neg (hL l hl)
  intro cl hcl
  unfold tseitin at hcl
  cases b with
  | true =>
      simp only [if_true] at hcl hg
      rcases List.mem_append.mp hcl with hm | hm
      · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
        show Clause.sat A #[-(g : Int), l] = true
        rcases Bool.eq_false_or_eq_true (A g) with hga | hga
        · have e : L.all (litVal A) = true := by rw [← hg]; exact hga
          exact clause_sat_of_mem (List.Mem.tail _ (List.Mem.head _)) (List.all_eq_true.mp e l hl)
        · have hv : litVal A (-(g : Int)) = true := by rw [hgn, hga, Bool.not_false]
          exact clause_sat_of_mem (List.Mem.head _) hv
      · rw [List.mem_singleton] at hm
        subst hm
        have ht : (#[(g : Int)] ++ (L.map fun l => -l).toArray).toList = (g : Int) :: L.map fun l => -l := by
          rw [Array.toList_append]; rfl
        rcases Bool.eq_false_or_eq_true (A g) with hga | hga
        · exact clause_sat_of_mem (by rw [ht]; exact List.Mem.head _) (hgp.trans hga)
        · have e : L.all (litVal A) = false := by rw [← hg]; exact hga
          obtain ⟨x, hx, hxt⟩ := List.all_eq_false.mp e
          rw [Bool.not_eq_true] at hxt
          have hv : litVal A (-x) = true := by rw [hneg x hx, hxt, Bool.not_false]
          exact clause_sat_of_mem (by rw [ht]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x, hx, rfl⟩)) hv
  | false =>
      simp only [Bool.false_eq_true, if_false] at hcl hg
      rcases List.mem_append.mp hcl with hm | hm
      · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
        show Clause.sat A #[(g : Int), -l] = true
        rcases Bool.eq_false_or_eq_true (A g) with hga | hga
        · exact clause_sat_of_mem (List.Mem.head _) (hgp.trans hga)
        · have e : L.any (litVal A) = false := by rw [← hg]; exact hga
          have hlf : litVal A l = false := by
            rcases Bool.eq_false_or_eq_true (litVal A l) with hlt | hlf
            · have et : L.any (litVal A) = true := List.any_eq_true.mpr ⟨l, hl, hlt⟩
              rw [et] at e
              nomatch e
            · exact hlf
          have hv : litVal A (-l) = true := by rw [hneg l hl, hlf, Bool.not_false]
          exact clause_sat_of_mem (List.Mem.tail _ (List.Mem.head _)) hv
      · rw [List.mem_singleton] at hm
        subst hm
        have ht : (#[-(g : Int)] ++ L.toArray).toList = (-(g : Int)) :: L := by
          rw [Array.toList_append]; rfl
        rcases Bool.eq_false_or_eq_true (A g) with hga | hga
        · have e : L.any (litVal A) = true := by rw [← hg]; exact hga
          obtain ⟨x, hx, hxt⟩ := List.any_eq_true.mp e
          exact clause_sat_of_mem (by rw [ht]; exact List.mem_cons_of_mem _ hx) hxt
        · have hv : litVal A (-(g : Int)) = true := by rw [hgn, hga, Bool.not_false]
          exact clause_sat_of_mem (by rw [ht]; exact List.Mem.head _) hv

theorem gate_cls_sat {p : Pos} {A : Assignment} {s : St} (hs : Inv s) (hg : Good p A s) :
    ∀ fc ∈ s.cls, fc.1 = .gate → fc.2.sat A = true := by
  intro fc hfc hfam
  obtain ⟨i, hi, b, L, hdef, hmem⟩ := hs.gates fc hfc hfam
  have hL : ∀ l ∈ L, l ≠ 0 := fun l hl =>
    Int.natAbs_pos.mp (hs.wf i hi b L hdef l hl).1
  have hg' : A (i + 1) = if b then L.all (litVal A) else L.any (litVal A) := by
    have h := hg i hi
    rw [hdef] at h
    exact h
  exact tseitin_sat A (i + 1) b L hL hg' (Nat.succ_pos i) fc.2 hmem

theorem a4_newVar_inv {s : St} (hs : Inv s) {d : VDef} (hd : ∀ b L, d = .gate b L → False) :
    Inv { s with nv := s.nv + 1, defs := s.defs.push d } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show s.nv + 1 = (s.defs.push d).size
    rw [Array.size_push, hs.nv]
  · intro b L g hcache
    obtain ⟨h1, h2, h3⟩ := hs.cache b L g hcache
    refine ⟨h1, Nat.le_trans h2 (Nat.le_succ _), ?_⟩
    have hnv := hs.nv
    have hg : g - 1 < s.defs.size := by omega
    rw [Array.getElem?_push_lt hg, ← Array.getElem?_eq_getElem hg]
    exact h3
  · intro i hi b L hdef
    have hdef' : (s.defs.push d)[i] = .gate b L := hdef
    have hi' : i < (s.defs.push d).size := hi
    rw [Array.size_push] at hi'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | heq
    · rw [Array.getElem_push_lt hlt] at hdef'
      exact hs.wf i hlt b L hdef'
    · subst heq
      rw [Array.getElem_push_eq] at hdef'
      exact absurd hdef' (hd b L)
  · intro fc hfc hfam
    obtain ⟨i, hi, b, L, hdef, hmem⟩ := hs.gates fc hfc hfam
    have hi2 : i < (s.defs.push d).size := by rw [Array.size_push]; omega
    exact ⟨i, hi2, b, L, by rw [Array.getElem_push_lt hi]; exact hdef, hmem⟩

theorem a4_newVar_ext (s : St) (d : VDef) :
    Ext s { s with nv := s.nv + 1, defs := s.defs.push d } := by
  refine ⟨?_, ?_, ⟨#[], by simp⟩⟩
  · show s.defs.size ≤ (s.defs.push d).size
    rw [Array.size_push]; omega
  · intro i h
    show (s.defs.push d)[i]? = some s.defs[i]
    rw [Array.getElem?_push_lt h]

theorem newVar_spec (s : St) (hs : Inv s) (d : VDef) (hd : ∀ b L, d = .gate b L → False) :
    Triple (newVar d) s [] fun v s' => v = s.nv + 1 ∧ s'.defs[s.nv]? = some d := by
  have hof : OnlyFams [.gate] s { s with nv := s.nv + 1, defs := s.defs.push d } := by
    intro fc hfc
    have hnc : NewCls s { s with nv := s.nv + 1, defs := s.defs.push d } = [] := by
      simp [NewCls, ← Array.length_toList]
    rw [hnc] at hfc
    exact (List.not_mem_nil hfc).elim
  have hq : s.nv + 1 = s.nv + 1 ∧
      ({ s with nv := s.nv + 1, defs := s.defs.push d }).defs[s.nv]? = some d :=
    ⟨rfl, by
      show (s.defs.push d)[s.nv]? = some d
      rw [hs.nv]
      exact Array.getElem?_push_size⟩
  exact ⟨a4_newVar_inv hs hd, a4_newVar_ext s d, hof, hq⟩

theorem a4_emit_inv {s : St} (hs : Inv s) {f : Fam} (hf : f ≠ .gate) (c : Clause) :
    Inv { s with cls := s.cls.push (f, c) } := by
  refine ⟨hs.nv, fun b L g hcache => hs.cache b L g hcache, fun i hi => hs.wf i hi, ?_⟩
  intro fc hfc hfam
  rcases Array.mem_push.mp hfc with hold | heq
  · exact hs.gates fc hold hfam
  · subst heq
    exact absurd hfam hf

theorem a4_emit_ext (s : St) (f : Fam) (c : Clause) :
    Ext s { s with cls := s.cls.push (f, c) } :=
  ⟨Nat.le_refl _, fun i h => by simp [h], ⟨#[(f, c)], by rw [Array.push_eq_append]⟩⟩

theorem a4_emit_newCls (s : St) (f : Fam) (c : Clause) :
    NewCls s { s with cls := s.cls.push (f, c) } = [(f, c)] := by
  show ((s.cls.push (f, c)).toList).drop s.cls.size = [(f, c)]
  rw [Array.toList_push, ← Array.length_toList, List.drop_left]

theorem a4_emit_of (s : St) (f : Fam) (c : Clause) :
    OnlyFams [.gate, f] s { s with cls := s.cls.push (f, c) } := by
  intro fc hfc
  rw [a4_emit_newCls] at hfc
  obtain rfl := List.mem_singleton.mp hfc
  exact List.Mem.tail _ (.head _)

theorem emit_spec (s : St) (hs : Inv s) (f : Fam) (hf : f ≠ .gate) (c : Clause) :
    Triple (emit f c) s [f] fun _ s' => NewCls s s' = [(f, c)] :=
  ⟨a4_emit_inv hs hf c, a4_emit_ext s f c, a4_emit_of s f c, a4_emit_newCls s f c⟩

theorem a4_any_filterMap (A : Assignment) (ws : List Wire) (h : Wire.tt ∉ ws) :
    (ws.filterMap (fun | .lit l => some l | _ => none)).any (litVal A) = ws.any (·.eval A) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      have hws : Wire.tt ∉ ws := fun hw => h (List.mem_cons_of_mem w hw)
      cases w with
      | tt => exact absurd (List.Mem.head ws) h
      | ff =>
          show (ws.filterMap (fun | .lit l => some l | _ => none)).any (litVal A) = ws.any (·.eval A)
          exact ih hws
      | lit l =>
          show (litVal A l || (ws.filterMap (fun | .lit l => some l | _ => none)).any (litVal A)) =
            (litVal A l || ws.any (·.eval A))
          rw [ih hws]

theorem emitW_spec (s : St) (hs : Inv s) (f : Fam) (hf : f ≠ .gate) (ws : List Wire) :
    Triple (emitW f ws) s [f] fun _ s' => ∀ fc ∈ NewCls s s', fc.1 = f ∧
      ∀ A, fc.2.sat A = ws.any (·.eval A) := by
  unfold emitW
  split
  · refine ⟨hs, ext_refl s, ?_, ?_⟩
    · intro fc hfc
      have hfc2 : fc ∈ NewCls s s := hfc
      rw [newCls_self] at hfc2
      exact (List.not_mem_nil hfc2).elim
    · intro fc hfc
      have hfc2 : fc ∈ NewCls s s := hfc
      rw [newCls_self] at hfc2
      exact (List.not_mem_nil hfc2).elim
  · rename_i hc
    have htt : Wire.tt ∉ ws := fun hm => hc (List.contains_iff_mem.mpr hm)
    obtain ⟨hinv, hext, hof, hq⟩ := emit_spec s hs f hf _
    refine ⟨hinv, hext, hof, ?_⟩
    intro fc hfc
    rw [hq] at hfc
    obtain rfl := List.mem_singleton.mp hfc
    refine ⟨rfl, fun A => ?_⟩
    show ((ws.filterMap (fun | .lit l => some l | _ => none)).toArray).any (litVal A) = ws.any (·.eval A)
    rw [List.any_toArray]
    exact a4_any_filterMap A ws htt

theorem require_spec (s : St) (hs : Inv s) (f : Fam) (hf : f ≠ .gate) (w : Wire) :
    Triple (require f w) s [f] fun _ s' => ∀ fc ∈ NewCls s s', fc.1 = f ∧ ∀ A, fc.2.sat A = w.eval A := by
  obtain ⟨hinv, hext, hof, hq⟩ := emitW_spec s hs f hf [w]
  refine ⟨hinv, hext, hof, ?_⟩
  intro fc hfc
  obtain ⟨hfam, hsat⟩ := hq fc hfc
  exact ⟨hfam, fun A => by rw [hsat A]; simp⟩

theorem a4_mem_of_mem_dedupSorted {a : Int} {l : List Int} (h : a ∈ dedupSorted l) : a ∈ l := by
  induction l with
  | nil => exact h
  | cons b t ih =>
      cases t with
      | nil => exact h
      | cons c u =>
          simp only [dedupSorted] at h
          split at h
          · exact List.mem_cons_of_mem _ (ih h)
          · rcases List.mem_cons.mp h with rfl | h
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih h)

theorem a4_mem_dedupSorted {a : Int} {l : List Int} (h : a ∈ l) : a ∈ dedupSorted l := by
  induction l with
  | nil => exact (List.not_mem_nil h).elim
  | cons b t ih =>
      cases t with
      | nil => exact h
      | cons c u =>
          simp only [dedupSorted]
          split
          · rename_i hbc
            rw [beq_iff_eq] at hbc
            rcases List.mem_cons.mp h with rfl | h
            · subst hbc
              exact ih (List.mem_cons_self)
            · exact ih h
          · rcases List.mem_cons.mp h with rfl | h
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih h)

theorem normLits_spec (ws : List Wire) :
    (∀ l ∈ normLits ws, ∃ w ∈ ws, w = .lit l) ∧ (∀ l, Wire.lit l ∈ ws → l ∈ normLits ws) := by
  constructor
  · intro l hl
    rw [normLits] at hl
    obtain ⟨w, hw, hgw⟩ :=
      List.mem_filterMap.mp (List.mem_mergeSort.mp (a4_mem_of_mem_dedupSorted hl))
    cases w with
    | tt => simp at hgw
    | ff => simp at hgw
    | lit l' =>
        obtain rfl := Option.some.inj hgw
        exact ⟨.lit l', hw, rfl⟩
  · intro l hl
    rw [normLits]
    exact a4_mem_dedupSorted (List.mem_mergeSort.mpr (List.mem_filterMap.mpr ⟨.lit l, hl, rfl⟩))

theorem runPureM {α : Type} (a : α) (st : St) : (pure a : M α).run st = (a, st) := rfl

theorem runBindM {α β : Type} (x : M α) (f : α → M β) (st : St) :
    (x >>= f).run st = (f (x.run st).1).run (x.run st).2 := rfl

theorem runGetM (st : St) : (get : M St).run st = (st, st) := rfl

theorem runNewVar (d : VDef) (st : St) :
    (newVar d).run st = (st.nv + 1, { st with nv := st.nv + 1, defs := st.defs.push d }) := rfl

theorem runEmitM (f : Fam) (c : Clause) (st : St) :
    (emit f c).run st = ((), { st with cls := st.cls.push (f, c) }) := rfl

theorem runModifyM (f : St → St) (st : St) : (modify f : M Unit).run st = ((), f st) := rfl

theorem tripleOfRun {α : Type} {x : M α} {s s' : St} {fs : List Fam} {Q : α → St → Prop} {a : α}
    (hr : x.run s = (a, s')) (hinv : Inv s') (hext : Ext s s') (hof : OnlyFams (.gate :: fs) s s')
    (hq : Q a s') : Triple x s fs Q := by
  simp only [Triple, hr]
  exact ⟨hinv, hext, hof, hq⟩

theorem tripleOfRunEq {α : Type} {x y : M α} {s : St} {fs : List Fam} {Q : α → St → Prop}
    (h : x.run s = y.run s) (ht : Triple y s fs Q) : Triple x s fs Q := by
  simp only [Triple, h]
  exact ht

theorem onlyFamsSelf (s : St) (fs : List Fam) : OnlyFams (.gate :: fs) s s := fun fc hfc => by
  rw [newCls_self] at hfc
  exact (List.not_mem_nil hfc).elim

theorem gateForInRun (L : List Int) (mk : Int → Clause) (st : St) :
    ((forIn L PUnit.unit (fun l _ =>
      (do emit .gate (mk l); pure (ForInStep.yield PUnit.unit)))) : M PUnit).run st =
      (PUnit.unit, { st with cls := st.cls ++ (L.map fun l => (.gate, mk l)).toArray }) := by
  induction L generalizing st with
  | nil => rfl
  | cons l L ih =>
    rw [List.forIn_cons]
    simp only [runBindM, runPureM, runEmitM]
    rw [ih]
    rw [List.map_cons, List.toArray_cons, ← Array.append_assoc, ← Array.push_eq_append]

theorem gateNewRunHit (s : St) (b : Bool) (L : List Int) (g : Nat) (h : s.cache[(b, L)]? = some g) :
    (gateNew b L).run s = (.lit (g : Int), s) := by
  simp only [gateNew, runBindM, runGetM]
  rw [h]
  rfl

theorem gateNewRunMissAnd (s : St) (L : List Int) (h : s.cache[(true, L)]? = none) :
    (gateNew true L).run s = (.lit ((s.nv + 1 : Nat) : Int),
      { s with nv := s.nv + 1,
               defs := s.defs.push (.gate true L),
               cls := (s.cls ++ (L.map fun l => (Fam.gate, #[-((s.nv + 1 : Nat) : Int), l])).toArray).push
                        (.gate, #[((s.nv + 1 : Nat) : Int)] ++ (L.map fun x => -x).toArray),
               cache := s.cache.insert (true, L) (s.nv + 1) }) := by
  simp only [gateNew, runBindM, runGetM]
  rw [h]
  simp only [runBindM, runPureM, runEmitM, runModifyM, runNewVar, gateForInRun]
  rw [if_pos trivial]
  simp only [runBindM, runPureM, runEmitM, runModifyM, gateForInRun]

theorem gateNewRunMissOr (s : St) (L : List Int) (h : s.cache[(false, L)]? = none) :
    (gateNew false L).run s = (.lit ((s.nv + 1 : Nat) : Int),
      { s with nv := s.nv + 1,
               defs := s.defs.push (.gate false L),
               cls := (s.cls ++ (L.map fun l => (Fam.gate, #[((s.nv + 1 : Nat) : Int), -l])).toArray).push
                        (.gate, #[-((s.nv + 1 : Nat) : Int)] ++ L.toArray),
               cache := s.cache.insert (false, L) (s.nv + 1) }) := by
  simp only [gateNew, runBindM, runGetM]
  rw [h]
  simp only [runBindM, runPureM, runEmitM, runModifyM, runNewVar, gateForInRun]
  rw [if_neg Bool.false_ne_true]
  simp only [runBindM, runPureM, runEmitM, runModifyM, gateForInRun]

def gateNewResultState (s : St) (b : Bool) (L : List Int) : St :=
  { s with nv := s.nv + 1, defs := s.defs.push (.gate b L),
           cls := s.cls ++ ((tseitin (s.nv + 1) b L).map fun c => (Fam.gate, c)).toArray,
           cache := s.cache.insert (b, L) (s.nv + 1) }

theorem toArrayAppendSingleton {α : Type} (l : List α) (x : α) :
    (l ++ [x]).toArray = l.toArray.push x := by
  apply Array.ext'
  rw [Array.toList_push, List.toList_toArray, List.toList_toArray]

theorem tagTseitinAnd (cls : Array (Fam × Clause)) (g : Nat) (L : List Int) :
    (cls ++ (L.map fun l => (Fam.gate, #[-(g : Int), l])).toArray).push
        (.gate, #[(g : Int)] ++ (L.map fun x => -x).toArray)
      = cls ++ ((tseitin g true L).map fun c => (Fam.gate, c)).toArray := by
  unfold tseitin
  rw [if_pos rfl, List.map_append, List.map_map, List.map_cons, List.map_nil,
    toArrayAppendSingleton, Array.push_append]
  rfl

theorem tagTseitinOr (cls : Array (Fam × Clause)) (g : Nat) (L : List Int) :
    (cls ++ (L.map fun l => (Fam.gate, #[(g : Int), -l])).toArray).push
        (.gate, #[-(g : Int)] ++ L.toArray)
      = cls ++ ((tseitin g false L).map fun c => (Fam.gate, c)).toArray := by
  unfold tseitin
  rw [if_neg Bool.false_ne_true, List.map_append, List.map_map, List.map_cons, List.map_nil,
    toArrayAppendSingleton, Array.push_append]
  rfl

theorem gateNewRunMiss (s : St) (b : Bool) (L : List Int) (h : s.cache[(b, L)]? = none) :
    (gateNew b L).run s = (.lit ((s.nv + 1 : Nat) : Int), gateNewResultState s b L) := by
  cases b with
  | false => rw [gateNewRunMissOr s L h, tagTseitinOr]; rfl
  | true => rw [gateNewRunMissAnd s L h, tagTseitinAnd]; rfl

theorem gateNewResultNv (s : St) (b : Bool) (L : List Int) :
    (gateNewResultState s b L).nv = s.nv + 1 := rfl

theorem gateNewResultCls (s : St) (b : Bool) (L : List Int) :
    (gateNewResultState s b L).cls =
      s.cls ++ ((tseitin (s.nv + 1) b L).map fun c => (Fam.gate, c)).toArray := rfl

theorem gateNewResultCache (s : St) (b : Bool) (L : List Int) :
    (gateNewResultState s b L).cache = s.cache.insert (b, L) (s.nv + 1) := rfl

theorem gateNewResultDefs (s : St) (b : Bool) (L : List Int) :
    (gateNewResultState s b L).defs = s.defs.push (.gate b L) := rfl

theorem gateNewFreshInv (s : St) (hs : Inv s) (b : Bool) (L : List Int)
    (hb : ∀ l ∈ L, 0 < l.natAbs ∧ l.natAbs ≤ s.nv) : Inv (gateNewResultState s b L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gateNewResultNv, gateNewResultDefs, Array.size_push, ← hs.nv]
  · intro b' L' g' hg'
    rw [gateNewResultCache, Std.HashMap.getElem?_insert] at hg'
    by_cases hkk : (b, L) == (b', L')
    · rw [if_pos hkk] at hg'
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp (eq_of_beq hkk)
      subst h1; subst h2
      have hge : g' = s.nv + 1 := (Option.some.inj hg').symm
      subst hge
      refine ⟨Nat.zero_lt_succ _, ?_, ?_⟩
      · rw [gateNewResultNv]; exact Nat.le_refl _
      · rw [gateNewResultDefs, hs.nv, Nat.add_sub_cancel]
        exact Array.getElem?_push_eq
    · rw [if_neg hkk] at hg'
      obtain ⟨hpos, hle, hd⟩ := hs.cache b' L' g' hg'
      refine ⟨hpos, ?_, ?_⟩
      · rw [gateNewResultNv]; exact Nat.le_trans hle (Nat.le_succ _)
      · rw [gateNewResultDefs, Array.getElem?_push]
        have hlt : g' - 1 < s.defs.size := (Array.getElem?_eq_some_iff.mp hd).1
        rw [if_neg (by omega)]
        exact hd
  · intro i hi b' L' hd
    have hd' : (gateNewResultState s b L).defs[i]? = some (.gate b' L') := by
      rw [Array.getElem?_eq_getElem hi, hd]
    rw [gateNewResultDefs, Array.getElem?_push] at hd'
    by_cases hie : i = s.defs.size
    · rw [if_pos hie] at hd'
      cases Option.some.inj hd'
      intro l hl
      obtain ⟨h1, h2⟩ := hb l hl
      exact ⟨h1, by rw [hie, ← hs.nv]; exact h2⟩
    · rw [if_neg hie] at hd'
      obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hd'
      exact hs.wf i hlt b' L' heq
  · intro fc hfc hfam
    rw [gateNewResultCls, Array.mem_append] at hfc
    rcases hfc with hfc | hfc
    · obtain ⟨i, hilt, b'', L'', hdef, hmem⟩ := hs.gates fc hfc hfam
      have e1 : (gateNewResultState s b L).defs[i]? = some (.gate b'' L'') := by
        rw [gateNewResultDefs, Array.getElem?_push, if_neg (by omega),
          Array.getElem?_eq_getElem hilt, hdef]
      have hi2 : i < (gateNewResultState s b L).defs.size := by
        rw [gateNewResultDefs, Array.size_push]; omega
      exact ⟨i, hi2, b'', L'', (Array.getElem?_eq_some_iff.mp e1).2, hmem⟩
    · obtain ⟨c, hc, hcfc⟩ := List.mem_map.mp (List.mem_toArray.mp hfc)
      have hfc2 : fc.2 = c := congrArg Prod.snd hcfc.symm
      have e1 : (gateNewResultState s b L).defs[s.defs.size]? = some (.gate b L) := by
        rw [gateNewResultDefs, Array.getElem?_push_eq]
      have hi2 : s.defs.size < (gateNewResultState s b L).defs.size := by
        rw [gateNewResultDefs, Array.size_push]; omega
      refine ⟨s.defs.size, hi2, b, L, (Array.getElem?_eq_some_iff.mp e1).2, ?_⟩
      rw [hfc2]; rw [hs.nv] at hc; exact hc

theorem gateNewFreshExt (s : St) (b : Bool) (L : List Int) : Ext s (gateNewResultState s b L) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gateNewResultDefs, Array.size_push]; omega
  · intro i hi
    rw [gateNewResultDefs, Array.getElem?_push, if_neg (by omega), Array.getElem?_eq_getElem hi]
  · exact ⟨_, gateNewResultCls s b L⟩

theorem gateNewFreshOnlyFams (s : St) (b : Bool) (L : List Int) :
    OnlyFams [.gate] s (gateNewResultState s b L) := by
  intro fc hfc
  have hN : NewCls s (gateNewResultState s b L) =
      ((tseitin (s.nv + 1) b L).map fun c => (Fam.gate, c)).toArray.toList := by
    show ((s.cls ++ ((tseitin (s.nv + 1) b L).map fun c => (Fam.gate, c)).toArray).toList).drop s.cls.size = _
    rw [Array.toList_append, ← Array.length_toList, List.drop_left, List.toList_toArray]
  rw [hN] at hfc
  obtain ⟨c, hc, hcfc⟩ := List.mem_map.mp hfc
  rw [← hcfc]
  exact List.mem_singleton_self _

theorem litValNat {A : Assignment} {n : Nat} (hn : 0 < n) : litVal A (n : Int) = A n := by
  rw [litVal, if_pos (Int.natCast_pos.mpr hn), Int.toNat_natCast]

theorem litValNeg {A : Assignment} {l : Int} (hl : l ≠ 0) : litVal A (-l) = !litVal A l := by
  obtain ⟨n, h | h⟩ : ∃ n : Nat, l = (n : Int) ∨ l = -(n : Int) := ⟨l.natAbs, Int.natAbs_eq l⟩
  · have hn : n ≠ 0 := fun e => hl (by rw [h, e, Int.natCast_zero])
    subst h
    rw [litVal, litVal,
      if_pos (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hn)),
      if_neg (show ¬ (0 : Int) < -(n : Int) from by
        have := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hn); omega),
      Int.natAbs_neg, Int.natAbs_natCast, Int.toNat_natCast]
  · have hn : n ≠ 0 := fun e => hl (by rw [h, e, Int.natCast_zero, Int.neg_zero])
    subst h
    rw [litVal, litVal,
      if_pos (show (0 : Int) < -(-(n : Int)) from by
        rw [Int.neg_neg]; exact Int.natCast_pos.mpr (Nat.pos_of_ne_zero hn)),
      if_neg (show ¬ (0 : Int) < -(n : Int) from by
        have := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hn); omega),
      Int.neg_neg, Int.toNat_natCast, Int.natAbs_neg, Int.natAbs_natCast, Bool.not_not]

theorem dedupAll (f : Int → Bool) : ∀ l : List Int, (dedupSorted l).all f = l.all f := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b t =>
      simp only [dedupSorted]
      by_cases hab : (a == b) = true
      · have hab' : a = b := eq_of_beq hab
        subst hab'
        rw [if_pos hab]
        rw [List.all_cons, List.all_cons, ← Bool.and_assoc, Bool.and_self, ih, List.all_cons]
      · rw [if_neg hab]
        rw [List.all_cons, List.all_cons, ih]

theorem dedupAny (f : Int → Bool) : ∀ l : List Int, (dedupSorted l).any f = l.any f := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b t =>
      simp only [dedupSorted]
      by_cases hab : (a == b) = true
      · have hab' : a = b := eq_of_beq hab
        subst hab'
        rw [if_pos hab]
        rw [List.any_cons, List.any_cons, ← Bool.or_assoc, Bool.or_self, ih, List.any_cons]
      · rw [if_neg hab]
        rw [List.any_cons, List.any_cons, ih]

theorem allEvalFilterMap (A : Assignment) (ws : List Wire) (h : Wire.ff ∉ ws) :
    ws.all (·.eval A) = (ws.filterMap fun | .lit l => some l | _ => none).all (litVal A) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have h' : Wire.ff ∉ ws := fun hw => h (List.mem_cons_of_mem w hw)
    have hwne : w ≠ Wire.ff := fun hw => h (hw ▸ List.mem_cons_self)
    cases w with
    | tt =>
      simp only [List.filterMap_cons]
      rw [List.all_cons, ih h']
      exact Bool.true_and _
    | ff => exact absurd rfl hwne
    | lit l =>
      simp only [List.filterMap_cons]
      rw [List.all_cons, List.all_cons, ih h']
      rfl

theorem anyEvalFilterMap (A : Assignment) (ws : List Wire) (h : Wire.tt ∉ ws) :
    ws.any (·.eval A) = (ws.filterMap fun | .lit l => some l | _ => none).any (litVal A) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have h' : Wire.tt ∉ ws := fun hw => h (List.mem_cons_of_mem w hw)
    have hwne : w ≠ Wire.tt := fun hw => h (hw ▸ List.mem_cons_self)
    cases w with
    | tt => exact absurd rfl hwne
    | ff =>
      simp only [List.filterMap_cons]
      rw [List.any_cons, ih h']
      exact Bool.false_or _
    | lit l =>
      simp only [List.filterMap_cons]
      rw [List.any_cons, List.any_cons, ih h']
      rfl

theorem allEvalNorm (A : Assignment) (ws : List Wire) (h : Wire.ff ∉ ws) :
    ws.all (·.eval A) = (normLits ws).all (litVal A) := by
  rw [allEvalFilterMap A ws h]
  unfold normLits
  rw [dedupAll, List.Perm.all_eq (List.mergeSort_perm _ _)]
  rfl

theorem anyEvalNorm (A : Assignment) (ws : List Wire) (h : Wire.tt ∉ ws) :
    ws.any (·.eval A) = (normLits ws).any (litVal A) := by
  rw [anyEvalFilterMap A ws h]
  unfold normLits
  rw [dedupAny, List.Perm.any_eq (List.mergeSort_perm _ _)]
  rfl

theorem memOfContainsTrue {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : l.contains a = true) : a ∈ l := List.contains_iff_mem.mp h

theorem notMemOfContainsFalse {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : l.contains a = false) : a ∉ l := by
  intro hm
  have h1 := List.contains_iff_mem.mpr hm
  rw [h] at h1
  exact absurd h1 (by decide)

theorem allEqFalseOfMem {α : Type} {f : α → Bool} {l : List α} (h : ∃ x ∈ l, f x = false) :
    l.all f = false := by
  obtain ⟨x, hx, hfx⟩ := h
  cases ha : l.all f with
  | false => rfl
  | true =>
    have h1 := List.all_eq_true.mp ha x hx
    rw [hfx] at h1
    exact absurd h1 (by decide)

theorem boundedNormLits {n : Nat} {ws : List Wire} (hw : ∀ w ∈ ws, w.Bounded n) :
    ∀ l ∈ normLits ws, 0 < l.natAbs ∧ l.natAbs ≤ n := by
  intro l hl
  obtain ⟨w, hwm, hwl⟩ := (normLits_spec ws).1 l hl
  subst hwl
  exact hw _ hwm

theorem allLitValFalseOfComp (A : Assignment) (L : List Int) (hz : ∀ l ∈ L, l ≠ 0)
    (h : ∃ l ∈ L, -l ∈ L) : L.all (litVal A) = false := by
  obtain ⟨l, hl, hnl⟩ := h
  cases hv : litVal A l with
  | false => exact allEqFalseOfMem ⟨l, hl, hv⟩
  | true => exact allEqFalseOfMem ⟨-l, hnl, by rw [litValNeg (hz l hl), hv]; rfl⟩

theorem anyLitValTrueOfComp (A : Assignment) (L : List Int) (hz : ∀ l ∈ L, l ≠ 0)
    (h : ∃ l ∈ L, -l ∈ L) : L.any (litVal A) = true := by
  obtain ⟨l, hl, hnl⟩ := h
  cases hv : litVal A l with
  | true => exact List.any_eq_true.mpr ⟨l, hl, hv⟩
  | false => exact List.any_eq_true.mpr ⟨-l, hnl, by rw [litValNeg (hz l hl), hv]; rfl⟩

theorem gateRunAbsorb (s : St) (b : Bool) (ws : List Wire)
    (h : ws.contains (if b then Wire.ff else Wire.tt) = true) :
    (gate b ws).run s = ((if b then Wire.ff else Wire.tt), s) := by
  simp only [gate]
  rw [h, if_pos rfl]
  rfl

theorem gateRunNil (s : St) (b : Bool) (ws : List Wire)
    (h : ws.contains (if b then Wire.ff else Wire.tt) = false) (hn : normLits ws = []) :
    (gate b ws).run s = ((if b then Wire.ff else Wire.tt).neg, s) := by
  simp only [gate]
  rw [h, if_neg Bool.false_ne_true, hn]
  rfl

theorem gateRunOne (s : St) (b : Bool) (ws : List Wire) (l : Int)
    (h : ws.contains (if b then Wire.ff else Wire.tt) = false) (hn : normLits ws = [l]) :
    (gate b ws).run s = (.lit l, s) := by
  simp only [gate]
  rw [h, if_neg Bool.false_ne_true, hn]
  rfl

theorem gateRunComp (s : St) (b : Bool) (ws : List Wire) (l₁ l₂ : Int) (t : List Int)
    (h : ws.contains (if b then Wire.ff else Wire.tt) = false) (hn : normLits ws = l₁ :: l₂ :: t)
    (hc : (l₁ :: l₂ :: t).any (fun l => (l₁ :: l₂ :: t).contains (-l)) = true) :
    (gate b ws).run s = ((if b then Wire.ff else Wire.tt), s) := by
  simp only [gate]
  rw [h, if_neg Bool.false_ne_true, hn]
  show (if ((l₁::l₂::t).any fun l => (l₁::l₂::t).contains (-l)) = true
        then pure (if b then Wire.ff else Wire.tt) else gateNew b (l₁::l₂::t)).run s
      = ((if b then Wire.ff else Wire.tt), s)
  rw [hc, if_pos rfl]
  rfl

theorem gateRunFresh (s : St) (b : Bool) (ws : List Wire) (l₁ l₂ : Int) (t : List Int)
    (h : ws.contains (if b then Wire.ff else Wire.tt) = false) (hn : normLits ws = l₁ :: l₂ :: t)
    (hc : (l₁ :: l₂:: t).any (fun l => (l₁ :: l₂ :: t).contains (-l)) = false) :
    (gate b ws).run s = (gateNew b (normLits ws)).run s := by
  simp only [gate]
  rw [h, if_neg Bool.false_ne_true, hn]
  show (if ((l₁::l₂::t).any fun l => (l₁::l₂::t).contains (-l)) = true
        then pure (if b then Wire.ff else Wire.tt) else gateNew b (l₁::l₂::t)).run s
      = (gateNew b (l₁::l₂::t)).run s
  rw [hc, if_neg Bool.false_ne_true]

theorem gateNewSpec (s : St) (hs : Inv s) (b : Bool) (L : List Int)
    (hb : ∀ l ∈ L, 0 < l.natAbs ∧ l.natAbs ≤ s.nv) :
    Triple (gateNew b L) s [] fun w s' => w.Bounded s'.nv ∧
      ∀ p A, Good p A s' → w.eval A = if b then L.all (litVal A) else L.any (litVal A) := by
  cases hc : s.cache[(b, L)]? with
  | some g =>
    obtain ⟨hpos, hle, hd⟩ := hs.cache b L g hc
    refine tripleOfRun (gateNewRunHit s b L g hc) hs (ext_refl s) (onlyFamsSelf s []) ⟨?_, ?_⟩
    · exact ⟨hpos, hle⟩
    · intro p A hg
      obtain ⟨hlt, hdeq⟩ := Array.getElem?_eq_some_iff.mp hd
      have hEq := hg (g - 1) hlt
      rw [show g - 1 + 1 = g from by omega] at hEq
      show litVal A (g : Int) = if b then L.all (litVal A) else L.any (litVal A)
      rw [litValNat hpos, hEq, hdeq]
      rfl
  | none =>
    refine tripleOfRun (gateNewRunMiss s b L hc) (gateNewFreshInv s hs b L hb)
      (gateNewFreshExt s b L) (gateNewFreshOnlyFams s b L) ⟨?_, ?_⟩
    · exact ⟨Nat.zero_lt_succ _, Nat.le_refl _⟩
    · intro p A hg
      have hlt : s.defs.size < (gateNewResultState s b L).defs.size := by
        show s.defs.size < (s.defs.push (.gate b L)).size
        rw [Array.size_push]; omega
      have hEq := hg s.defs.size hlt
      have hdeq : (gateNewResultState s b L).defs[s.defs.size]'hlt = .gate b L := Array.getElem_push_eq
      rw [hdeq] at hEq
      show litVal A ((s.nv + 1 : Nat) : Int) = if b then L.all (litVal A) else L.any (litVal A)
      rw [litValNat (Nat.zero_lt_succ _), hs.nv, hEq]
      rfl

theorem gate_spec (s : St) (hs : Inv s) (b : Bool) (ws : List Wire) (hw : ∀ w ∈ ws, w.Bounded s.nv) :
    Triple (gate b ws) s [] fun w s' => w.Bounded s'.nv ∧
      ∀ p A, Good p A s' → w.eval A = if b then ws.all (·.eval A) else ws.any (·.eval A) := by
  by_cases habs : ws.contains (if b then Wire.ff else Wire.tt) = true
  · refine tripleOfRun (gateRunAbsorb s b ws habs) hs (ext_refl s) (onlyFamsSelf s []) ⟨?_, ?_⟩
    · cases b <;> exact True.intro
    · intro p A _
      cases b with
      | true =>
        have hm := memOfContainsTrue habs
        show false = ws.all (·.eval A)
        exact (allEqFalseOfMem ⟨.ff, hm, rfl⟩).symm
      | false =>
        have hm := memOfContainsTrue habs
        show true = ws.any (·.eval A)
        exact (List.any_eq_true.mpr ⟨.tt, hm, rfl⟩).symm
  · have habs2 : ws.contains (if b then Wire.ff else Wire.tt) = false := by
      cases hc2 : ws.contains (if b then Wire.ff else Wire.tt) with
      | false => rfl
      | true => exact absurd hc2 habs
    cases hn : normLits ws with
    | nil =>
      refine tripleOfRun (gateRunNil s b ws habs2 hn) hs (ext_refl s) (onlyFamsSelf s []) ⟨?_, ?_⟩
      · cases b <;> exact True.intro
      · intro p A _
        cases b with
        | true =>
          show true = ws.all (·.eval A)
          rw [allEvalNorm A ws (notMemOfContainsFalse habs2), hn, List.all_nil]
        | false =>
          show false = ws.any (·.eval A)
          rw [anyEvalNorm A ws (notMemOfContainsFalse habs2), hn, List.any_nil]
    | cons l t =>
      cases t with
      | nil =>
        refine tripleOfRun (gateRunOne s b ws l habs2 hn) hs (ext_refl s) (onlyFamsSelf s []) ⟨?_, ?_⟩
        · obtain ⟨w, hwm, hwl⟩ := (normLits_spec ws).1 l (by rw [hn]; exact List.mem_singleton_self l)
          subst hwl
          exact hw _ hwm
        · intro p A _
          cases b with
          | true =>
            show litVal A l = ws.all (·.eval A)
            rw [allEvalNorm A ws (notMemOfContainsFalse habs2), hn, List.all_cons, List.all_nil,
              Bool.and_true]
          | false =>
            show litVal A l = ws.any (·.eval A)
            rw [anyEvalNorm A ws (notMemOfContainsFalse habs2), hn, List.any_cons, List.any_nil,
              Bool.or_false]
      | cons l₂ t₂ =>
        by_cases hcomp : (l :: l₂ :: t₂).any (fun x => (l :: l₂ :: t₂).contains (-x)) = true
        · refine tripleOfRun (gateRunComp s b ws l l₂ t₂ habs2 hn hcomp) hs (ext_refl s)
            (onlyFamsSelf s []) ⟨?_, ?_⟩
          · cases b <;> exact True.intro
          · intro p A _
            obtain ⟨x, hx, hcx⟩ := List.any_eq_true.mp hcomp
            have hnx : -x ∈ (l :: l₂ :: t₂) := List.contains_iff_mem.mp hcx
            have hz : ∀ y ∈ (l :: l₂ :: t₂), y ≠ 0 := by
              intro y hy
              exact Int.natAbs_pos.mp (boundedNormLits hw y (by rw [hn]; exact hy)).1
            cases b with
            | true =>
              show false = ws.all (·.eval A)
              rw [allEvalNorm A ws (notMemOfContainsFalse habs2), hn,
                allLitValFalseOfComp A _ hz ⟨x, hx, hnx⟩]
            | false =>
              show true = ws.any (·.eval A)
              rw [anyEvalNorm A ws (notMemOfContainsFalse habs2), hn,
                anyLitValTrueOfComp A _ hz ⟨x, hx, hnx⟩]
        · have hcomp2 : (l :: l₂ :: t₂).any (fun x => (l :: l₂ :: t₂).contains (-x)) = false := by
            cases hc2 : (l :: l₂ :: t₂).any (fun x => (l :: l₂ :: t₂).contains (-x)) with
            | false => rfl
            | true => exact absurd hc2 hcomp
          obtain ⟨hI, hE, hO, hB, hEv⟩ := gateNewSpec s hs b (normLits ws) (boundedNormLits hw)
          refine tripleOfRunEq (gateRunFresh s b ws l l₂ t₂ habs2 hn hcomp2)
            ⟨hI, hE, hO, hB, ?_⟩
          intro p A hg
          rw [hEv p A hg]
          cases b with
          | true => rw [allEvalNorm A ws (notMemOfContainsFalse habs2)]; rfl
          | false => rw [anyEvalNorm A ws (notMemOfContainsFalse habs2)]; rfl

theorem a6_neg_bounded {n : Nat} {w : Wire} (h : w.Bounded n) : w.neg.Bounded n := by
  cases w with
  | tt => trivial
  | ff => trivial
  | lit l =>
    obtain ⟨h1, h2⟩ := h
    show 0 < (-l).natAbs ∧ (-l).natAbs ≤ n
    rw [Int.natAbs_neg]
    exact ⟨h1, h2⟩

theorem a6_neg_eval (A : Assignment) {w : Wire} {n : Nat} (h : w.Bounded n) :
    w.neg.eval A = !w.eval A := by
  cases w with
  | tt => rfl
  | ff => rfl
  | lit l => exact litVal_neg (Int.natAbs_pos.mp h.1)

theorem a6_evalAll {ws : List Wire} {es : List Ex} {A : Assignment}
    (h : ws.map (fun w => w.eval A) = es.map (fun e => e.eval A)) :
    ws.all (·.eval A) = Ex.evalAll A es := by
  induction es generalizing ws with
  | nil =>
    cases ws with
    | nil => rfl
    | cons w ws => simp only [List.map_nil] at h; injection h
  | cons e es ih =>
    cases ws with
    | nil => simp only [List.map_nil, List.map_cons] at h; injection h
    | cons w ws =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h0, htail⟩ := h
      rw [List.all_cons, h0, ih htail]
      rfl

theorem a6_evalAny {ws : List Wire} {es : List Ex} {A : Assignment}
    (h : ws.map (fun w => w.eval A) = es.map (fun e => e.eval A)) :
    ws.any (·.eval A) = Ex.evalAny A es := by
  induction es generalizing ws with
  | nil =>
    cases ws with
    | nil => rfl
    | cons w ws => simp only [List.map_nil] at h; injection h
  | cons e es ih =>
    cases ws with
    | nil => simp only [List.map_nil, List.map_cons] at h; injection h
    | cons w ws =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h0, htail⟩ := h
      rw [List.any_cons, h0, ih htail]
      rfl

theorem a6_boundedAll_mono {n n' : Nat} (h : n ≤ n') {es : List Ex} (he : Ex.BoundedAll n es) :
    Ex.BoundedAll n' es :=
  ex_boundedAll_mono_aux h he

mutual
theorem compileAll_spec (s : St) (hs : Inv s) (es : List Ex) (he : Ex.BoundedAll s.nv es) :
    Triple (compileAll es) s [] fun ws s' =>
      ws.length = es.length ∧ (∀ w ∈ ws, w.Bounded s'.nv) ∧
      ∀ p A, Good p A s' → ws.map (fun w => w.eval A) = es.map (fun e => e.eval A) := by
  cases es with
  | nil =>
    show Triple (pure ([] : List Wire)) s [] _
    exact triple_pure _ s hs _ _
      ⟨rfl, fun w hw => (List.not_mem_nil hw).elim, fun _ _ _ => rfl⟩
  | cons e es =>
    have h1 : e.Bounded s.nv := he.1
    have h2 : Ex.BoundedAll s.nv es := he.2
    show Triple (compile e >>= fun w => compileAll es >>= fun ws => pure (w :: ws)) s [] _
    refine triple_bind (compile_spec s hs e h1) ?_
    intro w s₁ hinv₁ hext₁ _ hQ1
    obtain ⟨hbd1, heval1⟩ := hQ1
    have hle : s.nv ≤ s₁.nv := by
      rw [hs.nv, hinv₁.nv]
      exact hext₁.defs_le
    refine triple_bind (compileAll_spec s₁ hinv₁ es (a6_boundedAll_mono hle h2)) ?_
    intro ws s₂ hinv₂ hext₂ _ hQ2
    obtain ⟨hlen, hbd, hcorr⟩ := hQ2
    show Triple (pure (w :: ws)) s₂ [] _
    have hle2 : s₁.nv ≤ s₂.nv := by
      rw [hinv₁.nv, hinv₂.nv]
      exact hext₂.defs_le
    refine triple_pure _ s₂ hinv₂ _ _ ⟨?_, ?_, ?_⟩
    · show (w :: ws).length = (e :: es).length
      rw [List.length_cons, List.length_cons, hlen]
    · intro w' hw'
      rw [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact wire_bounded_mono hle2 hbd1
      · exact hbd w' hw'
    · intro p A hgood
      show (w :: ws).map (fun w => w.eval A) = (e :: es).map (fun e => e.eval A)
      rw [List.map_cons, List.map_cons, heval1 p A (good_mono hext₂ hgood), hcorr p A hgood]
termination_by sizeOf es
decreasing_by all_goals (try subst_vars; simp_all; try omega)

theorem compile_spec (s : St) (hs : Inv s) (e : Ex) (he : e.Bounded s.nv) :
    Triple (compile e) s [] fun w s' => w.Bounded s'.nv ∧ ∀ p A, Good p A s' → w.eval A = e.eval A := by
  cases e with
  | k b =>
    show Triple (pure (if b then Wire.tt else Wire.ff)) s [] _
    refine triple_pure _ s hs _ _ ⟨?_, ?_⟩
    · cases b <;> trivial
    · intro p A _
      cases b <;> rfl
  | v l =>
    show Triple (pure (Wire.lit l)) s [] _
    exact triple_pure _ s hs _ _ ⟨he, fun _ _ _ => rfl⟩
  | not e =>
    show Triple (compile e >>= fun w => pure w.neg) s [] _
    refine triple_bind (compile_spec s hs e he) ?_
    intro w s₁ hinv₁ _ _ hQ
    obtain ⟨hbd, heval⟩ := hQ
    show Triple (pure w.neg) s₁ [] _
    refine triple_pure _ s₁ hinv₁ _ _ ⟨a6_neg_bounded hbd, fun p A hgood => ?_⟩
    calc w.neg.eval A = !w.eval A := a6_neg_eval A hbd
      _ = !e.eval A := by rw [heval p A hgood]
  | and es =>
    show Triple (compileAll es >>= fun ws => gate true ws) s [] _
    refine triple_bind (compileAll_spec s hs es he) ?_
    intro ws s₁ hinv₁ _ _ hQ
    obtain ⟨_, hbd, hcorr⟩ := hQ
    refine triple_mono (gate_spec s₁ hinv₁ true ws hbd) (fun f hf => hf) ?_
    intro w s₂ _ hext₁₂ hQg
    obtain ⟨hbdw, hevalw⟩ := hQg
    refine ⟨hbdw, fun p A hgood => ?_⟩
    calc w.eval A = if true then ws.all (·.eval A) else ws.any (·.eval A) := hevalw p A hgood
      _ = ws.all (·.eval A) := rfl
      _ = Ex.evalAll A es := a6_evalAll (hcorr p A (good_mono hext₁₂ hgood))
  | or es =>
    show Triple (compileAll es >>= fun ws => gate false ws) s [] _
    refine triple_bind (compileAll_spec s hs es he) ?_
    intro ws s₁ hinv₁ _ _ hQ
    obtain ⟨_, hbd, hcorr⟩ := hQ
    refine triple_mono (gate_spec s₁ hinv₁ false ws hbd) (fun f hf => hf) ?_
    intro w s₂ _ hext₁₂ hQg
    obtain ⟨hbdw, hevalw⟩ := hQg
    refine ⟨hbdw, fun p A hgood => ?_⟩
    calc w.eval A = if false then ws.all (·.eval A) else ws.any (·.eval A) := hevalw p A hgood
      _ = ws.any (·.eval A) := rfl
      _ = Ex.evalAny A es := a6_evalAny (hcorr p A (good_mono hext₁₂ hgood))
termination_by sizeOf e
decreasing_by all_goals (try subst_vars; simp_all; try omega)
end

theorem a7_getElem!_eq_getElem {α : Type} [Inhabited α] {xs : Array α} {i : Nat} (h : i < xs.size) :
    xs[i]! = xs[i] := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

theorem a7_getElem!_mem {α : Type} [Inhabited α] {xs : Array α} {i : Nat} (h : i < xs.size) :
    xs[i]! ∈ xs := by
  rw [a7_getElem!_eq_getElem h]
  exact Array.getElem_mem h

theorem counterRow_aux (js : List Nat) :
    ∀ (s : St) (hs : Inv s) (l : Wire) (prev cur : Array Wire),
      l.Bounded s.nv →
      (∀ w ∈ prev, w.Bounded s.nv) →
      (∀ w ∈ cur, w.Bounded s.nv) →
      (∀ j ∈ js, 1 ≤ j ∧ j < prev.size) →
      Triple (counterRow l prev js cur) s [] fun out s' =>
        out.size = cur.size + js.length ∧ (∀ w ∈ out, w.Bounded s'.nv) ∧
        ∀ p A, Good p A s' → (∀ i (h : i < cur.size), out[i]!.eval A = cur[i].eval A) ∧
          ∀ n (h : n < js.length), out[cur.size + n]!.eval A =
            (prev[js[n] - 1]!.eval A && l.eval A || prev[js[n]]!.eval A) := by
  induction js with
  | nil =>
    intro s hs l prev cur _hl _hp hc _hj
    exact triple_pure cur s hs [] _
      ⟨rfl, hc, fun _ _ _ =>
        ⟨fun i h => by rw [a7_getElem!_eq_getElem h],
         fun n h => absurd h (Nat.not_lt_zero n)⟩⟩
  | cons j js ih =>
    intro s hs l prev cur hl hp hc hj
    have hj0 := hj j List.mem_cons_self
    have hb1 : prev[j - 1]!.Bounded s.nv := hp _ (a7_getElem!_mem (by omega))
    have hb0 : prev[j]!.Bounded s.nv := hp _ (a7_getElem!_mem hj0.2)
    have hw1 : ∀ w ∈ [l, prev[j - 1]!], w.Bounded s.nv := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hl
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact hb1
        · exact (List.not_mem_nil hw).elim
    refine triple_bind (gate_spec s hs true [l, prev[j - 1]!] hw1) ?_
    intro a s1 hinv1 hext1 _ hqa
    have hnv1 : s.nv ≤ s1.nv := by rw [hs.nv, hinv1.nv]; exact hext1.defs_le
    have hw2 : ∀ w ∈ [prev[j]!, a], w.Bounded s1.nv := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact wire_bounded_mono hnv1 hb0
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact hqa.1
        · exact (List.not_mem_nil hw).elim
    refine triple_bind (gate_spec s1 hinv1 false [prev[j]!, a] hw2) ?_
    intro o s2 hinv2 hext2 _ hqo
    have hext12 : Ext s s2 := ext_trans hext1 hext2
    have hnv2 : s.nv ≤ s2.nv := by rw [hs.nv, hinv2.nv]; exact hext12.defs_le
    have hc2 : ∀ w ∈ cur.push o, w.Bounded s2.nv := by
      intro w hw
      rcases Array.mem_push.mp hw with hw | rfl
      · exact wire_bounded_mono hnv2 (hc w hw)
      · exact hqo.1
    refine triple_mono (ih s2 hinv2 l prev (cur.push o) (wire_bounded_mono hnv2 hl)
        (fun w hw => wire_bounded_mono hnv2 (hp w hw)) hc2
        (fun j' hm => hj j' (List.mem_cons_of_mem j hm))) (fun g hg => hg) ?_
    intro out s3 hinv3 hext3 hout
    obtain ⟨hsize, hbound, heval⟩ := hout
    refine ⟨?_, hbound, fun p A hgood => ?_⟩
    · rw [Array.size_push] at hsize
      rw [List.length_cons]
      omega
    · have hg2 : Good p A s2 := good_mono hext3 hgood
      have hg1 : Good p A s1 := good_mono hext2 hg2
      have hga : a.eval A = (l.eval A && prev[j - 1]!.eval A) := by
        have h := hqa.2 p A hg1
        have hif : (if true then [l, prev[j - 1]!].all (·.eval A)
            else [l, prev[j - 1]!].any (·.eval A)) = [l, prev[j - 1]!].all (·.eval A) := rfl
        rw [hif] at h
        simpa only [List.all_cons, List.all_nil, Bool.and_true] using h
      have hgo : o.eval A = (prev[j]!.eval A || a.eval A) := by
        have h := hqo.2 p A hg2
        have hif : (if false then [prev[j]!, a].all (·.eval A)
            else [prev[j]!, a].any (·.eval A)) = [prev[j]!, a].any (·.eval A) := rfl
        rw [hif] at h
        simpa only [List.any_cons, List.any_nil, Bool.or_false] using h
      obtain ⟨hprev, hrow⟩ := heval p A hgood
      refine ⟨fun i h => ?_, fun n h => ?_⟩
      · have h1 := hprev i (by rw [Array.size_push]; omega)
        rwa [Array.getElem_push_lt h] at h1
      · cases n with
        | zero =>
          have h1 : out[cur.size]!.eval A = o.eval A := by
            have h2 := hprev cur.size (by rw [Array.size_push]; omega)
            rwa [Array.getElem_push_eq] at h2
          rw [Nat.add_zero, h1, hgo, hga]
          show (prev[j]!.eval A || (l.eval A && prev[j - 1]!.eval A)) =
            (prev[j - 1]!.eval A && l.eval A || prev[j]!.eval A)
          rw [Bool.or_comm, Bool.and_comm]
        | succ n =>
          have h2 := hrow n (Nat.lt_of_succ_lt_succ h)
          rw [show cur.size + (n + 1) = (cur.push o).size + n from by rw [Array.size_push]; omega]
          exact h2

theorem counterRow_spec (s : St) (hs : Inv s) (l : Wire) (prev cur : Array Wire) (js : List Nat)
    (hl : l.Bounded s.nv) (hp : ∀ w ∈ prev, w.Bounded s.nv) (hc : ∀ w ∈ cur, w.Bounded s.nv)
    (hj : ∀ j ∈ js, 1 ≤ j ∧ j < prev.size) :
    Triple (counterRow l prev js cur) s [] fun out s' =>
      out.size = cur.size + js.length ∧ (∀ w ∈ out, w.Bounded s'.nv) ∧
      ∀ p A, Good p A s' → (∀ i (h : i < cur.size), out[i]!.eval A = cur[i].eval A) ∧
        ∀ n (h : n < js.length), out[cur.size + n]!.eval A =
          (prev[js[n] - 1]!.eval A && l.eval A || prev[js[n]]!.eval A) :=
  counterRow_aux js s hs l prev cur hl hp hc hj

theorem a7_count_succ (m j : Nat) :
    (decide (j ≤ m) || decide (j + 1 ≤ m) : Bool) = decide (j + 1 ≤ m + 1) := by
  by_cases h : j ≤ m
  · rw [decide_eq_true_iff.mpr h, Bool.true_or, decide_eq_true_iff.mpr (by omega : j + 1 ≤ m + 1)]
  · rw [decide_eq_false_iff_not.mpr h, Bool.false_or,
      decide_eq_false_iff_not.mpr (by omega : ¬ j + 1 ≤ m),
      decide_eq_false_iff_not.mpr (by omega : ¬ j + 1 ≤ m + 1)]

theorem counter_go :
    ∀ (L' : List Wire) (Ls : List Wire) (s : St) (hs : Inv s) (k : Nat) (acc : Array Wire),
      acc.size = k + 1 →
      (∀ w ∈ acc, w.Bounded s.nv) →
      (∀ p A, Good p A s → ∀ j (hj : j ≤ k), acc[j]!.eval A =
        decide (j ≤ (Ls.filter (·.eval A)).length)) →
      (∀ w ∈ L', w.Bounded s.nv) →
      Triple (L'.foldlM (fun prev l => counterRow l prev (List.range' 1 k) #[.tt]) acc) s []
        fun c s' => c.size = k + 1 ∧ (∀ w ∈ c, w.Bounded s'.nv) ∧
          ∀ p A, Good p A s' → ∀ j (hj : j ≤ k), c[j]!.eval A =
            decide (j ≤ ((Ls ++ L').filter (·.eval A)).length) := by
  intro L'
  induction L' with
  | nil =>
    intro Ls s hs k acc hsize hacc hev _hL
    rw [List.foldlM_nil]
    refine triple_pure acc s hs [] _ ⟨hsize, hacc, ?_⟩
    intro p A hgood j hj
    rw [List.append_nil]
    exact hev p A hgood j hj
  | cons l L'' ih =>
    intro Ls s hs k acc hsize hacc hev hL
    rw [List.foldlM_cons]
    have hl : l.Bounded s.nv := hL l List.mem_cons_self
    have hL'' : ∀ w ∈ L'', w.Bounded s.nv := fun w hw => hL w (List.mem_cons_of_mem l hw)
    have hcur : ∀ w ∈ (#[.tt] : Array Wire), w.Bounded s.nv := by
      intro w hw
      have hw' : w = Wire.tt := by
        have h := Array.mem_def.mp hw
        rw [List.toList_toArray] at h
        exact List.mem_singleton.mp h
      subst hw'
      exact True.intro
    have hjs : ∀ m ∈ List.range' 1 k, 1 ≤ m ∧ m < acc.size := by
      intro m hm
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hm
      refine ⟨by omega, ?_⟩
      rw [hsize]
      omega
    refine triple_bind (counterRow_spec s hs l acc #[.tt] (List.range' 1 k) hl hacc hcur hjs) ?_
    intro out s2 hinv2 hext2 _ hrow
    obtain ⟨hsize2, hbnd2, hev2⟩ := hrow
    have hsize2' : out.size = k + 1 := by
      have hs1 : (#[Wire.tt] : Array Wire).size = 1 := rfl
      rw [List.length_range', hs1] at hsize2
      omega
    have hnv : s.nv ≤ s2.nv := by rw [hs.nv, hinv2.nv]; exact hext2.defs_le
    have hL''2 : ∀ w ∈ L'', w.Bounded s2.nv := fun w hw => wire_bounded_mono hnv (hL'' w hw)
    have hev2' : ∀ p A, Good p A s2 → ∀ j (hj : j ≤ k), out[j]!.eval A =
        decide (j ≤ ((Ls ++ [l]).filter (·.eval A)).length) := by
      intro p A hgood j hj
      have hgood1 : Good p A s := good_mono hext2 hgood
      obtain ⟨hprev, hrow⟩ := hev2 p A hgood
      have hcount : ((Ls ++ [l]).filter (·.eval A)).length =
          (Ls.filter (·.eval A)).length + ([l].filter (·.eval A)).length := by
        rw [List.filter_append, List.length_append]
      cases j with
      | zero =>
        have h0 : out[0]!.eval A = true := hprev 0 Nat.zero_lt_one
        rw [h0]
        exact (decide_eq_true_iff.mpr (Nat.zero_le _)).symm
      | succ j =>
        have hjk : j < k := by omega
        have h1 := hrow j (by rw [List.length_range']; exact hjk)
        simp only [List.getElem_range'] at h1
        rw [Nat.one_mul, Nat.add_sub_cancel_left] at h1
        rw [show (#[Wire.tt] : Array Wire).size = 1 from rfl, Nat.add_comm 1 j] at h1
        have a1 : acc[j]!.eval A = decide (j ≤ (Ls.filter (·.eval A)).length) :=
          hev p A hgood1 j (by omega)
        have a2 : acc[j + 1]!.eval A = decide (j + 1 ≤ (Ls.filter (·.eval A)).length) :=
          hev p A hgood1 (j + 1) hj
        rw [h1, a1, a2]
        cases heq : l.eval A with
        | true =>
          have hfl : [l].filter (·.eval A) = [l] := by
            rw [List.filter_cons_of_pos heq, List.filter_nil]
          rw [Bool.and_true, hcount, hfl]
          exact a7_count_succ _ _
        | false =>
          have hnot : ¬ (·.eval A) l = true := by
            show ¬ l.eval A = true
            intro h'
            rw [heq] at h'
            exact Bool.noConfusion h'
          have hfl : [l].filter (·.eval A) = [] := by
            rw [List.filter_cons_of_neg hnot, List.filter_nil]
          rw [Bool.and_false, Bool.false_or, hcount, hfl]
          rfl
    refine triple_mono (ih (Ls ++ [l]) s2 hinv2 k out hsize2' hbnd2 hev2' hL''2) (fun g hg => hg) ?_
    intro c s3 hinv3 hext3 hb
    obtain ⟨h1, h2, h3⟩ := hb
    refine ⟨h1, h2, fun p A hgood j hj => ?_⟩
    rw [h3 p A hgood j hj, List.append_assoc]
    rfl

theorem counter_spec (s : St) (hs : Inv s) (L : List Wire) (k : Nat) (hL : ∀ w ∈ L, w.Bounded s.nv) :
    Triple (counter L k) s [] fun c s' => c.size = k + 1 ∧ (∀ w ∈ c, w.Bounded s'.nv) ∧
      ∀ p A, Good p A s' → ∀ j ≤ k, c[j]!.eval A = decide (j ≤ (L.filter (·.eval A)).length) := by
  have h1 : (#[Wire.tt] ++ Array.replicate k Wire.ff : Array Wire).size = k + 1 := by
    have hs1 : (#[Wire.tt] : Array Wire).size = 1 := rfl
    rw [Array.size_append, Array.size_replicate, hs1]
    omega
  have h2 : ∀ w ∈ (#[Wire.tt] ++ Array.replicate k Wire.ff : Array Wire), w.Bounded s.nv := by
    intro w hw
    rcases Array.mem_append.mp hw with hw | hw
    · have hw' := Array.mem_def.mp hw
      rw [List.toList_toArray] at hw'
      obtain rfl := List.mem_singleton.mp hw'
      exact True.intro
    · have hw' := Array.mem_def.mp hw
      rw [Array.toList_replicate] at hw'
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hw'
      exact True.intro
  have h3 : ∀ p A, Good p A s → ∀ j (hj : j ≤ k),
      (#[Wire.tt] ++ Array.replicate k Wire.ff : Array Wire)[j]!.eval A =
        decide (j ≤ (([] : List Wire).filter (·.eval A)).length) := by
    intro p A _ j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have hb : (#[Wire.tt] ++ Array.replicate k Wire.ff : Array Wire)[0]! = Wire.tt := by
        rw [a7_getElem!_eq_getElem (by rw [h1]; omega),
          Array.getElem_append_left Nat.zero_lt_one]
        rfl
      rw [hb]
      show true = decide (0 ≤ (([] : List Wire).filter (·.eval A)).length)
      exact (decide_eq_true_iff.mpr (Nat.zero_le _)).symm
    · have hb : (#[Wire.tt] ++ Array.replicate k Wire.ff : Array Wire)[j]! = Wire.ff := by
        rw [a7_getElem!_eq_getElem (by rw [h1]; omega),
          Array.getElem_append_right hjpos,
          Array.getElem_replicate (h := by
            rw [Array.size_replicate, show (#[Wire.tt] : Array Wire).size = 1 from rfl]
            omega)]
      rw [hb]
      show false = decide (j ≤ (([] : List Wire).filter (·.eval A)).length)
      exact (decide_eq_false_iff_not.mpr (by omega : ¬ j ≤ 0)).symm
  exact counter_go L [] s hs k _ h1 h2 h3 hL

theorem atleast_spec (s : St) (hs : Inv s) (f : Fam) (hf : f ≠ .gate) (L : List Wire) (k : Nat)
    (hL : ∀ w ∈ L, w.Bounded s.nv) :
    Triple (atleast f L k) s [f] fun _ s' => ∀ p A, Good p A s' →
      ∀ fc ∈ NewCls s s', fc.1 = f → (fc.2.sat A = true ↔ k ≤ (L.filter (·.eval A)).length) := by
  obtain ⟨hc_inv, hc_ext, hc_of, hc_q⟩ := counter_spec s hs L k hL
  obtain ⟨hr_inv, hr_ext, hr_of, hr_q⟩ :=
    require_spec ((counter L k).run s).2 hc_inv f hf (((counter L k).run s).1[k]!)
  refine ⟨hr_inv, ext_trans hc_ext hr_ext, ?_, ?_⟩
  · intro fc hfc
    have hfc3 : fc ∈ NewCls s (((require f (((counter L k).run s).1[k]!)).run
        ((counter L k).run s).2).2) := hfc
    rw [newCls_trans hc_ext hr_ext] at hfc3
    rcases List.mem_append.mp hfc3 with h | h
    · have h1 := hc_of fc h
      rcases List.mem_cons.mp h1 with h2 | h2
      · rw [h2]
        exact List.mem_cons_self
      · exact (List.not_mem_nil h2).elim
    · exact hr_of fc h
  · intro p A hgood fc hfc hfam
    have hfc3 : fc ∈ NewCls s (((require f (((counter L k).run s).1[k]!)).run
        ((counter L k).run s).2).2) := hfc
    rw [newCls_trans hc_ext hr_ext] at hfc3
    rcases List.mem_append.mp hfc3 with h | h
    · have h1 := hc_of fc h
      rcases List.mem_cons.mp h1 with h2 | h2
      · exact absurd (hfam.symm.trans h2) hf
      · exact (List.not_mem_nil h2).elim
    · obtain ⟨_, hsat⟩ := hr_q fc h
      have hek : (((counter L k).run s).1[k]!).eval A =
          decide (k ≤ (L.filter (·.eval A)).length) :=
        hc_q.2.2 p A (good_mono hr_ext hgood) k (Nat.le_refl k)
      rw [hsat A, hek]
      exact decide_eq_true_iff

theorem atmost_spec (s : St) (hs : Inv s) (f : Fam) (hf : f ≠ .gate) (L : List Wire) (k : Nat)
    (hL : ∀ w ∈ L, w.Bounded s.nv) :
    Triple (atmost f L k) s [f] fun _ s' => ∀ p A, Good p A s' →
      ∀ fc ∈ NewCls s s', fc.1 = f → (fc.2.sat A = true ↔ (L.filter (·.eval A)).length ≤ k) := by
  obtain ⟨hc_inv, hc_ext, hc_of, hc_q⟩ := counter_spec s hs L (k + 1) hL
  obtain ⟨hr_inv, hr_ext, hr_of, hr_q⟩ :=
    require_spec ((counter L (k + 1)).run s).2 hc_inv f hf
      (((((counter L (k + 1)).run s).1)[k + 1]!).neg)
  have hmem : (((counter L (k + 1)).run s).1)[k + 1]! ∈ ((counter L (k + 1)).run s).1 :=
    a7_getElem!_mem (by rw [hc_q.1]; omega)
  refine ⟨hr_inv, ext_trans hc_ext hr_ext, ?_, ?_⟩
  · intro fc hfc
    have hfc3 : fc ∈ NewCls s (((require f ((((counter L (k + 1)).run s).1)[k + 1]!.neg)).run
        ((counter L (k + 1)).run s).2).2) := hfc
    rw [newCls_trans hc_ext hr_ext] at hfc3
    rcases List.mem_append.mp hfc3 with h | h
    · have h1 := hc_of fc h
      rcases List.mem_cons.mp h1 with h2 | h2
      · rw [h2]
        exact List.mem_cons_self
      · exact (List.not_mem_nil h2).elim
    · exact hr_of fc h
  · intro p A hgood fc hfc hfam
    have hfc3 : fc ∈ NewCls s (((require f ((((counter L (k + 1)).run s).1)[k + 1]!.neg)).run
        ((counter L (k + 1)).run s).2).2) := hfc
    rw [newCls_trans hc_ext hr_ext] at hfc3
    rcases List.mem_append.mp hfc3 with h | h
    · have h1 := hc_of fc h
      rcases List.mem_cons.mp h1 with h2 | h2
      · exact absurd (hfam.symm.trans h2) hf
      · exact (List.not_mem_nil h2).elim
    · obtain ⟨_, hsat⟩ := hr_q fc h
      have hneg : ∀ A, ((((counter L (k + 1)).run s).1)[k + 1]!.neg).eval A =
          !(((counter L (k + 1)).run s).1)[k + 1]!.eval A := by
        intro A
        cases hw : (((counter L (k + 1)).run s).1)[k + 1]! with
        | tt => rfl
        | ff => rfl
        | lit l =>
          have hb := hc_q.2.1 _ hmem
          rw [hw] at hb
          obtain ⟨hpos, -⟩ := hb
          exact litVal_neg (Int.natAbs_pos.mp hpos)
      have hek : (((counter L (k + 1)).run s).1[k + 1]!).eval A =
          decide (k + 1 ≤ (L.filter (·.eval A)).length) :=
        hc_q.2.2 p A (good_mono hr_ext hgood) (k + 1) (Nat.le_refl _)
      rw [hsat A, hneg A, hek]
      constructor
      · intro h
        have hd : decide (k + 1 ≤ (L.filter (·.eval A)).length) = false := by
          cases hb : decide (k + 1 ≤ (L.filter (·.eval A)).length) with
          | true =>
            rw [hb] at h
            exact absurd h (by decide)
          | false => rfl
        exact Nat.lt_succ_iff.mp (Nat.not_le.mp (decide_eq_false_iff_not.mp hd))
      · intro h
        have hn : ¬ k + 1 ≤ (L.filter (·.eval A)).length := by omega
        rw [decide_eq_false_iff_not.mpr hn]
        rfl

end Chess.All63
