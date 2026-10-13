import ChessProof.C364.EncodeSound
import ChessProof.C364.Trust

namespace Chess.C364

open Chess.C364.Fm Chess.C364.Enc Chess.C364.Tree

def hasTree (wb : Sq × Sq) : Bool := Data.trees.any fun T => T.kw == wb.1 && T.kb == wb.2

def b1Direct : List (Sq × Sq) := reps.filter fun wb => !hasTree wb

set_option maxRecDepth 100000 in
theorem b0_eq : Data.b0 = reps := by decide +kernel

set_option maxRecDepth 100000 in
theorem b1_eq : Data.b1 = b1Direct := by decide +kernel

theorem trees_n : ∀ T ∈ Data.trees, 1 ≤ T.n ∧ T.n ≤ 23 := by decide +kernel

set_option maxRecDepth 100000 in
theorem certRecords_length : certRecords.length = 6921 := by decide +kernel

structure Cert : Prop where
  b0 : ∀ wb ∈ reps, Unsat (F wb.1 wb.2 20 0)
  b1 : ∀ wb ∈ b1Direct, Unsat (F wb.1 wb.2 22 1)
  trees : ∀ T ∈ Data.trees, ∀ x ∈ T.obligations, Unsat (T.enc.formula.add x)

theorem encodeCfg_layout (g : Cfg) :
    (encodeCfg g).layout = ((layoutM g).run { nv := 0, roles := #[] }).1 := by
  unfold encodeCfg
  generalize (layoutM g).run { nv := 0, roles := #[] } = x
  obtain ⟨Ly, a⟩ := x
  rfl

theorem forIn_push_size {α : Type}
    (f : α → Array (Array AttLayer) → AM (ForInStep (Array (Array AttLayer))))
    (hf : ∀ t AT a, ∃ l0 l1 s', (f t AT).run a = (.yield (AT.push #[l0, l1]), s')) :
    ∀ (l : List α) (init : Array (Array AttLayer)) (a : Alloc),
      ((forIn l init f).run a).1.size = init.size + l.length := by
  intro l
  induction l with
  | nil =>
    intro init a
    rw [List.forIn_nil]
    rfl
  | cons x xs ih =>
    intro init a
    rw [List.forIn_cons, run_bind]
    obtain ⟨l0, l1, s', hfx⟩ := hf x init a
    rw [hfx]
    show ((forIn xs (init.push #[l0, l1]) f).run s').1.size = init.size + (xs.length + 1)
    rw [ih (init.push _) s', Array.size_push]
    omega

theorem AT_size (g : Cfg) : (encodeCfg g).layout.AT.size = g.n + 1 := by
  rw [encodeCfg_layout]
  unfold layoutM
  simp only [run_bind]
  by_cases hn : 1 ≤ g.n
  · rw [ite_eq_left hn]
    simp only [run_bind]
    rw [run_pure]
    rw [forIn_push_size _ (by
      intro t AT a
      rw [run_bind, run_bind, run_pure]
      exact ⟨_, _, _, rfl⟩)]
    simp [List.length_range]
  · rw [ite_eq_right (by omega : ¬g.n ≥ 1)]
    simp only [run_bind]
    rw [run_pure]
    rw [forIn_push_size _ (by
      intro t AT a
      rw [run_bind, run_bind, run_pure]
      exact ⟨_, _, _, rfl⟩)]
    simp [List.length_range]

theorem attAtL_entries_nil (g : Cfg) (t x : Nat) (ht : g.n < t) : (attAtL g t x).entries = [] := by
  have hsz : (encodeCfg g).layout.AT.size = g.n + 1 := AT_size g
  show (((encodeCfg g).layout.AT.getD t #[]).getD x default).entries = []
  rw [Array.getD_eq_getD_getElem? (xs := (encodeCfg g).layout.AT) (i := t) (d := #[]),
    Array.getElem?_eq_none (by rw [hsz]; omega : (encodeCfg g).layout.AT.size ≤ t)]
  show ((#[] : Array AttLayer).getD x default).entries = []
  rw [Array.getD_eq_getD_getElem? (xs := (#[] : Array AttLayer)) (i := x) (d := default),
    Array.getElem?_eq_none (by simp : (#[] : Array AttLayer).size ≤ x)]
  rfl

theorem attAt_eq_A (g : Cfg) (t x : Nat) : attAt (encodeCfg g) t x = (attAtL g t x).A := rfl

theorem cubesOK_encode (w b : Sq) (n m : Nat) : CubesOK (encode w b n m) := by
  show CubesOK (encodeCfg (cfgOf w b n m))
  intro sp k hk l hl
  cases sp with
  | caps =>
    simp only [cubes, List.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    simp only [List.nil_append] at hl
    simp only [capsCubes, List.mem_flatMap, List.mem_range, List.mem_map] at hc
    obtain ⟨wgt, -, S, hS, rfl⟩ := hc
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨t, ht, rfl⟩ := hl
    have hcap : (capVars (encodeCfg (cfgOf w b n m))).getD t 0 = (plyAt (cfgOf w b n m) t).CAP :=
      caps_layout (cfgOf w b n m) t ht
    have hpos : 0 < (plyAt (cfgOf w b n m) t).CAP := (roles_CAPPROMO (cfgOf w b n m) t ht).1.1
    by_cases hct : S.contains t = true
    · rw [ite_eq_left hct, hcap]
      show (plyAt (cfgOf w b n m) t).CAP ≠ (0 : Int)
      omega
    · rw [ite_eq_right hct, hcap]
      show (-(plyAt (cfgOf w b n m) t).CAP : Int) ≠ (0 : Int)
      omega
  | chk k0 =>
    simp only [cubes, List.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    simp only [List.nil_append] at hl
    by_cases hk0 : k0 + 1 ≤ n
    · simp only [chkCubes, List.mem_map, List.mem_mergeSort] at hc
      obtain ⟨⟨q, a⟩, he, rfl⟩ := hc
      simp only [List.mem_singleton] at hl
      rw [attAt_eq_A] at he
      simp only [AttLayer.A, List.mem_map] at he
      obtain ⟨en, hen, heq⟩ := he
      obtain ⟨cs, -, hrole, -⟩ :=
        (roles_entries (cfgOf w b n m) (k0 + 1) (1 - (cfgOf w b n m).col k0)
          (by show k0 + 1 ≤ n; omega)
          (by
            show 1 - k0 % 2 < 2
            have hmod := Nat.mod_lt k0 (by decide : 2 > 0)
            omega)).2 en hen
      have hpos : 0 < en.a := hrole.1
      have hae : en.a = a := congrArg Prod.snd heq
      rw [hl]
      show a ≠ (0 : Int)
      omega
    · have hempty : attAt (encodeCfg (cfgOf w b n m)) (k0 + 1)
          (1 - (encodeCfg (cfgOf w b n m)).cfg.col k0) = [] := by
        rw [attAt_eq_A, AttLayer.A, attAtL_entries_nil (cfgOf w b n m) (k0 + 1) _ (by
          show n < k0 + 1
          omega)]
        rfl
      rw [chkCubes, hempty, List.mergeSort_nil, List.map_nil] at hc
      exact absurd hc (by simp)

def SplitOk (g : Cfg) : Split → Bool
  | .caps => g.m == 1
  | .chk k => k + 1 ≤ g.n

def cubeCount (g : Cfg) : Split → Nat
  | .caps => g.n + 1
  | .chk k => (attAlts g (1 - k % 2)).length

mutual
def FitsShape (g : Cfg) : Shape → Bool
  | .leaf => true
  | .node sp kids => SplitOk g sp && kids.length == cubeCount g sp && FitsShapes g kids
def FitsShapes (g : Cfg) : List Shape → Bool
  | [] => true
  | s :: ss => FitsShape g s && FitsShapes g ss
end

set_option maxRecDepth 100000 in
theorem trees_fit : ∀ T ∈ Data.trees, FitsShape (cfgOf T.kw T.kb T.n 1) T.shape = true := by decide +kernel

theorem combos_zero_length (l : List Nat) : (combos 0 l).length = 1 := by
  cases l <;> rfl

theorem combos_one_length (l : List Nat) : (combos 1 l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [combos, ih]

theorem capsCubes_length (E : Encoding) (hm : E.cfg.m = 1) : (capsCubes E).length = E.cfg.n + 1 := by
  simp [capsCubes, hm, List.range_succ, combos_zero_length, combos_one_length]
  omega

theorem chkCubes_length (g : Cfg) (k : Nat) (hk : k + 1 ≤ g.n) :
    (chkCubes (encodeCfg g) k).length = (attAlts g (1 - k % 2)).length := by
  have h := congrArg List.length (roles_entries g (k + 1) (1 - k % 2) hk (by omega)).1
  simp only [List.length_map] at h
  simp only [chkCubes, List.length_map, List.length_mergeSort, attAt, Cfg.col]
  simpa [attAtL, Layout.att, AttLayer.A] using h

theorem cubes_length (g : Cfg) (U : List Lit) (sp : Split) (hs : SplitOk g sp = true) :
    (cubes (encodeCfg g) U sp).length = cubeCount g sp := by
  cases sp with
  | caps =>
    simp only [SplitOk, beq_iff_eq] at hs
    simp only [cubes, List.length_map, cubeCount]
    exact capsCubes_length _ hs
  | chk k =>
    simp only [SplitOk, decide_eq_true_eq] at hs
    simp only [cubes, List.length_map, cubeCount]
    exact chkCubes_length g k hs

mutual
theorem obls_length (g : Cfg) : ∀ (s : Shape) (U : List Lit), FitsShape g s = true →
    (obls (encodeCfg g) U s).length = s.size
  | .leaf, U, _ => by simp [obls, Shape.size]
  | .node sp kids, U, h => by
    simp only [FitsShape, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hs, hk⟩, hf⟩ := h
    have hl := cubes_length g U sp hs
    simp only [obls, List.length_cons, Shape.size]
    rw [oblsKids_length g kids (cubes (encodeCfg g) U sp) (by omega) hf]
    omega
theorem oblsKids_length (g : Cfg) : ∀ (ss : List Shape) (ks : List (List Lit)), ks.length = ss.length →
    FitsShapes g ss = true → (oblsKids (encodeCfg g) ks ss).length = Shape.sizes ss
  | [], ks, hk, _ => by simp at hk; subst hk; simp [oblsKids, Shape.sizes]
  | s :: ss, ks, hk, h => by
    simp only [FitsShapes, Bool.and_eq_true] at h
    cases ks with
    | nil => simp at hk
    | cons k kt =>
      simp only [oblsKids, List.length_append, List.headD_cons, List.tail_cons, Shape.sizes]
      rw [obls_length g s k h.1, oblsKids_length g ss kt (by simpa using hk) h.2]
end

theorem obligations_length (T : TreeRec) (hT : T ∈ Data.trees) : T.obligations.length = T.shape.size :=
  obls_length (cfgOf T.kw T.kb T.n 1) T.shape [] (trees_fit T hT)

theorem B0_of_cert (h : Cert) : BoundB 0 19 :=
  boundB_of_noChain 0 19 fun wb hwb => noChain_of_unsat wb.1 wb.2 20 0 (by decide) (h.b0 wb hwb)

theorem noChain23_of_cert (h : Cert) (wb : Sq × Sq) (hwb : wb ∈ reps) : NoChain wb.1 wb.2 23 1 := by
  by_cases ht : hasTree wb = true
  · obtain ⟨T, hT, hTw⟩ := List.any_eq_true.mp ht
    have hn := trees_n T hT
    simp only [Bool.and_eq_true, beq_iff_eq] at hTw
    have hu : Unsat (F T.kw T.kb T.n 1) := tree_sound T.enc (cubesOK_encode _ _ _ _) T.shape (h.trees T hT)
    have := noChain_of_unsat T.kw T.kb T.n 1 hn.1 hu
    rw [hTw.1, hTw.2] at this
    exact noChain_mono _ _ _ _ _ this hn.2
  · have hd : wb ∈ b1Direct := List.mem_filter.mpr ⟨hwb, by simpa using ht⟩
    exact noChain_mono _ _ 22 23 1 (noChain_of_unsat wb.1 wb.2 22 1 (by decide) (h.b1 wb hd)) (by decide)

theorem B1_of_cert (h : Cert) : BoundB 1 22 :=
  boundB_of_noChain 1 22 fun wb hwb => noChain23_of_cert h wb hwb

theorem theoremA (h : Cert) : BoundB 0 19 ∧ BoundB 1 22 := ⟨B0_of_cert h, B1_of_cert h⟩

theorem checks_le_364_of_cert (h : Cert) :
    ∀ (p : Pos) (ms : List Move), Reachable p → IsCheckSeq p ms → ms.length ≤ 364 :=
  checks_le_364_of_B (B0_of_cert h) (B1_of_cert h)

theorem Formula.add_nil (F : Formula) : F.add [] = F := by
  cases F; simp [Formula.add]

theorem cert_of_records (h : ∀ r ∈ certRecords, Unsat r.formula) : Cert := by
  refine ⟨fun wb hwb => ?_, fun wb hwb => ?_, fun T hT x hx => ?_⟩
  · rw [← b0_eq] at hwb
    have := h _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (f := fun wb : Sq × Sq =>
      ({ kw := wb.1, kb := wb.2, n := 20, m := 0, extra := [] } : Record)) hwb)))
    simpa [Record.formula, Formula.add_nil] using this
  · rw [← b1_eq] at hwb
    have := h _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (f := fun wb : Sq × Sq =>
      ({ kw := wb.1, kb := wb.2, n := 22, m := 1, extra := [] } : Record)) hwb)))
    simpa [Record.formula, Formula.add_nil] using this
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : j < T.shape.size := obligations_length T hT ▸ hj
    have hr : ({ kw := T.kw, kb := T.kb, n := T.n, m := 1, extra := T.obligations.getD j [] } : Record) ∈ certRecords :=
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨T, hT, List.mem_map.mpr ⟨j, List.mem_range.mpr hj', rfl⟩⟩)
    have := h _ hr
    simp only [Record.formula, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
    simpa [TreeRec.enc, F] using this

theorem records_of_facts (U : UnsatFacts364) : ∀ r ∈ certRecords, Unsat r.formula := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hu := U.unsat i (certRecords_length ▸ hi)
  simp only [R364, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hu
  exact Fm.Formula.unsat_of_toCnf _ hu

theorem checks_le_364_of_records (h : ∀ r ∈ certRecords, Unsat r.formula) :
    ∀ (p : Pos) (ms : List Move), Reachable p → IsCheckSeq p ms → ms.length ≤ 364 :=
  checks_le_364_of_cert (cert_of_records h)

theorem checks_le_364_of_facts (U : UnsatFacts364) :
    ∀ (p : Pos) (ms : List Move), Reachable p → IsCheckSeq p ms → ms.length ≤ 364 :=
  checks_le_364_of_records (records_of_facts U)

end Chess.C364
