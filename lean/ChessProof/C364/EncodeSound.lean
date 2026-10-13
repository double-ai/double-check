import ChessProof.C364.Symmetry
import ChessProof.C364.Encode

namespace Chess.C364.Enc

open Chess Chess.C364 Chess.C364.Fm

def toSq (s : Nat) : Sq := ⟨s % 64, Nat.mod_lt _ (by decide)⟩

def colIdx : Color → Nat
  | .white => 0
  | .black => 1

def kindIdx : Kind → Nat
  | .pawn => 0
  | .knight => 1
  | .bishop => 2
  | .rook => 3
  | .queen => 4
  | .king => 5

def code : Option Piece → Nat
  | none => 10
  | some ⟨_, .king⟩ => 11
  | some q => 5 * colIdx q.color + kindIdx q.kind

def colorOf (x : Nat) : Color := if x = 0 then .white else .black

structure Run where
  pos : Nat → Pos
  mv : Nat → Move

def runOf (p : Pos) (ms : List Move) : Run where
  pos t := after p (ms.take t)
  mv t := ms.getD t default

def Sem.val (g : Cfg) (r : Run) : Sem → Bool
  | .x t s k => code ((r.pos t).board (toSq s)) == k
  | .fr t s => (r.mv t).src.val == s
  | .to t s => (r.mv t).dst.val == s
  | .mp t p => ((r.pos t).board (r.mv t).src).any fun q => kindIdx q.kind == p
  | .rt t p => ((r.pos t).board (r.mv t).src).any fun q => kindIdx ((r.mv t).promo.getD q.kind) == p
  | .cap t => isCapture (r.pos t) (r.mv t)
  | .promo t => (r.mv t).promo.isSome
  | .eps t s => (r.pos t).ep == some (toSq s)
  | .epr t v => epVictim (r.pos t) (r.mv t) == some (toSq v)
  | .att t y s =>
    match (r.pos t).board (toSq s) with
    | some q => q.color == colorOf (1 - y) && (attacks (r.pos t).board (toSq s) q).contains (toSq (g.K y))
    | none => false
  | .clear t ss => ss.all fun s => (r.pos t).board (toSq s) == none
  | .ch t s =>
    (r.mv t).src.val == s || (r.mv t).dst.val == s || epVictim (r.pos t) (r.mv t) == some (toSq s)

def Fa2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Fa2 R as bs
  | _, _ => False

def Role.val (g : Cfg) (r : Run) : Role → Bool
  | .sem a => a.val g r
  | .conj rs => rs.all (·.val g r)
  | .ladder rs i => (rs.take (i + 1)).any (·.val g r)
  | .count rs i j => decide (j + 1 ≤ ((rs.take (i + 1)).filter (·.val g r)).length)

def intended (E : Encoding) (r : Run) : Assign := fun v =>
  match E.alloc.roles[v - 1]? with
  | some ro => ro.val E.cfg r
  | none => false

def HasRole (E : Encoding) (v : Int) (ro : Role) : Prop :=
  0 < v ∧ E.alloc.roles[v.toNat - 1]? = some ro

theorem clause_eval₁ (σ : Assign) (a : Int) : Clause.eval σ [a] = Lit.eval σ a := by simp [Clause.eval]

theorem clause_eval₂ (σ : Assign) (a b : Int) :
    Clause.eval σ [a, b] = (Lit.eval σ a || Lit.eval σ b) := by simp [Clause.eval]

theorem clause_eval₃ (σ : Assign) (a b c : Int) :
    Clause.eval σ [a, b, c] = (Lit.eval σ a || (Lit.eval σ b || Lit.eval σ c)) := by
  simp [Clause.eval]

theorem getD_mem {α : Type} : ∀ (l : List α) (d : α) (i : Nat), i < l.length → l.getD i d ∈ l
  | _ :: _, _, 0, _ => List.mem_cons_self
  | _ :: as, d, i + 1, h => List.mem_cons_of_mem _ (getD_mem as d i (by simpa using h))
  | [], _, _, h => absurd h (by simp)

theorem fa2_length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Fa2 R as bs → as.length = bs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Fa2] at h
  | _ :: _, [], h => by simp [Fa2] at h
  | _ :: as, _ :: bs, h => by
      have h1 := fa2_length_eq (show Fa2 R as bs from (show _ ∧ _ from h).2)
      rw [List.length_cons, List.length_cons, h1]

theorem fa2_getD {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β} (h : Fa2 R as bs) (i : Nat),
      i < as.length → ∀ (a₀ : α) (b₀ : β), R (as.getD i a₀) (bs.getD i b₀)
  | _ :: as, _ :: bs, h, 0, _, a₀, b₀ => (show _ ∧ _ from h).1
  | _ :: as, _ :: bs, h, i + 1, hi, a₀, b₀ =>
      fa2_getD (show Fa2 R as bs from (show _ ∧ _ from h).2) i (by simpa using hi) a₀ b₀
  | [], _, _, _, hi, _, _ => by simp at hi
  | _ :: _, [], h, _, _, _, _ => by simp [Fa2] at h

theorem fa2_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Fa2 R as bs →
      ∀ {a : α}, a ∈ as → ∃ b, b ∈ bs ∧ R a b
  | [], _, _, _, ha => by simp at ha
  | x :: as, y :: ys, h, _, ha => by
      have h1 : R x y ∧ Fa2 R as ys := h
      rcases List.mem_cons.mp ha with rfl | hx
      · exact ⟨y, List.mem_cons_self, h1.1⟩
      · obtain ⟨b, hb, hr⟩ := fa2_mem_left h1.2 hx
        exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩
  | _ :: _, [], h, _, _ => by simp [Fa2] at h

theorem take_succ_getD : ∀ (l : List Bool) (i : Nat), i < l.length →
    l.take (i + 1) = l.take i ++ [l.getD i false]
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => by
      show _ :: l.take (i + 1) = _ :: (l.take i ++ [l.getD i false])
      rw [take_succ_getD l i (by simpa using h)]
  | [], _, h => by simp at h

theorem filter_take_succ (l : List Bool) (i : Nat) (hi : i < l.length) :
    ((l.take (i + 1)).filter id).length = ((l.take i).filter id).length + (l.getD i false).toNat := by
  rw [take_succ_getD l i hi, List.filter_append, List.length_append]
  cases h : l.getD i false <;> rfl

theorem any_take_succ (l : List Bool) (i : Nat) (hi : i < l.length) :
    (l.take (i + 1)).any id = ((l.take i).any id || l.getD i false) := by
  rw [take_succ_getD l i hi, List.any_append]
  cases h : l.getD i false <;> simp

theorem cnt_mono' (vals : List Bool) {a b : Nat} (h : a ≤ b) :
    ((vals.take a).filter id).length ≤ ((vals.take b).filter id).length :=
  ((List.take_sublist_take_left h).filter id).length_le

theorem filter_ge_two (l : List Bool) (i : Nat) (hi : i < l.length) (hvi : l.getD i false = true)
    (hpre : (l.take i).any id = true) : 2 ≤ (l.filter id).length := by
  rw [List.any_eq_true] at hpre
  obtain ⟨b, hb, hbv⟩ := hpre
  have h1 : 0 < ((l.take i).filter id).length :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨hb, hbv⟩)
  have h2 : ((l.take (i + 1)).filter id).length = ((l.take i).filter id).length + 1 := by
    rw [filter_take_succ l i hi, hvi, Bool.toNat_true]
  have h3 : ((l.take (i + 1)).filter id).length ≤ (l.filter id).length :=
    ((List.take_sublist _ l).filter id).length_le
  omega

theorem amo_pairs_sound (σ : Assign) : ∀ (lits : List Int) (vals : List Bool),
    Fa2 (fun l v => Lit.eval σ l = v) lits vals →
    (∀ l ∈ lits, l ≠ 0) → (vals.filter id).length ≤ 1 →
    ∀ c ∈ (pairs lits).map (fun (a, b) => [-a, -b]), Clause.eval σ c = true
  | [], _, _, _, _, _, hc => by simp [pairs] at hc
  | _ :: _, [], h, _, _, _, _ => by simp [Fa2] at h
  | a :: lits, va :: vals, h, hz, hamo, c, hc => by
      have h1 : Lit.eval σ a = va ∧ Fa2 (fun l v => Lit.eval σ l = v) lits vals := h
      have hz' : ∀ l ∈ lits, l ≠ 0 := fun l hl => hz l (List.mem_cons_of_mem _ hl)
      have hamo' : (vals.filter id).length ≤ 1 := by
        cases va with
        | false =>
            have hfa : ((false :: vals).filter id) = vals.filter id :=
              List.filter_cons_of_neg (by decide)
            rw [hfa] at hamo
            exact hamo
        | true =>
            have hfa : ((true :: vals).filter id) = true :: vals.filter id :=
              List.filter_cons_of_pos rfl
            rw [hfa, List.length_cons] at hamo
            omega
      simp only [pairs, List.map_append, List.mem_append] at hc
      rcases hc with hcl | hcr
      · simp only [List.map_map, List.mem_map] at hcl
        obtain ⟨b, hb, hbc⟩ := hcl
        have hbc' : [-a, -b] = c := hbc
        rw [← hbc']
        obtain ⟨vb, hvb, hvbv⟩ := fa2_mem_left h1.2 hb
        rw [clause_eval₂, lit_neg_eval σ a (hz a (List.mem_cons_self)),
          lit_neg_eval σ b (hz' b hb), h1.1, hvbv]
        cases va with
        | false => rfl
        | true =>
            cases vb with
            | false => rfl
            | true =>
                exfalso
                have hfb : 0 < (vals.filter id).length :=
                  List.length_pos_of_mem (List.mem_filter.mpr ⟨hvb, by decide⟩)
                have hfa : ((true :: vals).filter id) = true :: vals.filter id :=
                  List.filter_cons_of_pos rfl
                rw [hfa, List.length_cons] at hamo
                omega
      · exact amo_pairs_sound σ lits vals h1.2 hz' hamo' c hcr


theorem lit_pos (E : Encoding) (r : Run) (v : Int) (ro : Role) (h : HasRole E v ro) :
    Lit.eval (intended E r) v = ro.val E.cfg r := by
  obtain ⟨hv, hro⟩ := h
  show (if 0 < v then (intended E r) v.toNat else !(intended E r) v.natAbs) = ro.val E.cfg r
  rw [ite_eq_left hv]
  simp only [intended, hro]

theorem lit_neg (E : Encoding) (r : Run) (v : Int) (ro : Role) (h : HasRole E v ro) :
    Lit.eval (intended E r) (-v) = !ro.val E.cfg r := by
  have hv : 0 < v := h.1
  rw [lit_neg_eval _ _ (by omega), lit_pos E r v ro h]

theorem amo_sound (σ : Assign) (lits lad : List Int) (vals : List Bool)
    (hz : ∀ l ∈ lits, l ≠ 0) (hzl : ∀ l ∈ lad, l ≠ 0)
    (hl : Fa2 (fun l v => Lit.eval σ l = v) lits vals) (hamo : (vals.filter id).length ≤ 1)
    (hlad : 8 < lits.length → lad.length = lits.length - 1 ∧
      ∀ i, i < lad.length → Lit.eval σ (lad.getD i 0) = (vals.take (i + 1)).any id) :
    ∀ c ∈ amoCls lits lad, Clause.eval σ c = true := by
  intro c hc
  by_cases h8 : lits.length ≤ 8
  · simp only [amoCls, ite_eq_left h8] at hc
    exact amo_pairs_sound σ lits vals hl hz hamo c hc
  · have h8' : 8 < lits.length := by omega
    obtain ⟨hladlen, hladv⟩ := hlad h8'
    have hlen : vals.length = lits.length := (fa2_length_eq hl).symm
    simp only [amoCls, ite_eq_right h8, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨i, hi, hci⟩ := hc
    have hv : Lit.eval σ (lits.getD i 0) = vals.getD i false := fa2_getD hl i hi 0 false
    have hxz : lits.getD i 0 ≠ 0 := hz _ (getD_mem _ _ _ hi)
    by_cases hin : i + 1 < lits.length
    · have hsi : i < lad.length := by omega
      have hsv : Lit.eval σ (lad.getD i 0) = (vals.take (i + 1)).any id := hladv i hsi
      have hsucc := any_take_succ vals i (by omega)
      rw [ite_eq_left hin] at hci
      by_cases hi0 : i = 0
      · subst hi0
        rw [ite_eq_left rfl] at hci
        have hci2 : c = [-lits.getD 0 0, lad.getD 0 0] := List.mem_singleton.mp hci
        subst hci2
        rw [clause_eval₂, lit_neg_eval σ _ hxz, hv, hsv,
          hsucc]
        simp only [List.take_zero, List.any_nil, Bool.false_or]
        cases hb : vals.getD 0 false <;> simp [hb]
      · rw [ite_eq_right hi0] at hci
        have hspi : i - 1 < lad.length := by omega
        have hs0 : lad.getD (i - 1) 0 ≠ 0 := hzl _ (getD_mem _ _ _ hspi)
        have hspv : Lit.eval σ (lad.getD (i - 1) 0) = (vals.take i).any id := by
          have h := hladv (i - 1) hspi
          rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at h
        rcases List.mem_cons.mp hci with hcc | hci
        · subst hcc
          rw [clause_eval₂, lit_neg_eval σ _ hxz, hv, hsv, hsucc]
          cases hb : vals.getD i false <;> cases hp : (vals.take i).any id <;> simp [hb, hp]
        · rcases List.mem_cons.mp hci with hcc | hcc
          · subst hcc
            rw [clause_eval₂, lit_neg_eval σ _ hs0, hspv, hsv, hsucc]
            cases hb : vals.getD i false <;> cases hp : (vals.take i).any id <;> simp [hb, hp]
          · have hcc2 : c = [-lits.getD i 0, -lad.getD (i - 1) 0] := List.mem_singleton.mp hcc
            subst hcc2
            rw [clause_eval₂, lit_neg_eval σ _ hxz, lit_neg_eval σ _ hs0, hv, hspv]
            cases hvt : vals.getD i false <;> cases hpt : (vals.take i).any id
            · rfl
            · rfl
            · rfl
            · exfalso
              have h2 := filter_ge_two vals i (by omega) hvt hpt
              omega
    · have hieq : i + 1 = lits.length := by omega
      rw [ite_eq_right hin] at hci
      have hci2 : c = [-lits.getD i 0, -lad.getD (i - 1) 0] := List.mem_singleton.mp hci
      subst hci2
      have hspi : i - 1 < lad.length := by omega
      have hs0 : lad.getD (i - 1) 0 ≠ 0 := hzl _ (getD_mem _ _ _ hspi)
      have hspv : Lit.eval σ (lad.getD (i - 1) 0) = (vals.take i).any id := by
        have h := hladv (i - 1) hspi
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at h
      rw [clause_eval₂, lit_neg_eval σ _ hxz, lit_neg_eval σ _ hs0, hv, hspv]
      cases hvt : vals.getD i false <;> cases hpt : (vals.take i).any id
      · rfl
      · rfl
      · rfl
      · exfalso
        have h2 := filter_ge_two vals i (by omega) hvt hpt
        omega


theorem counter_sound (σ : Assign) (g : Cfg) (caps : List Int) (S : List (List Int)) (vals : List Bool)
    (hne : caps ≠ []) (hz : ∀ c ∈ caps, c ≠ 0) (hzS : ∀ r ∈ S, ∀ l ∈ r, l ≠ 0)
    (hl : Fa2 (fun l v => Lit.eval σ l = v) caps vals)
    (hm : (vals.filter id).length ≤ g.m)
    (hS : g.m ≠ 0 → S.length = caps.length ∧ ∀ i, i < caps.length → (S.getD i []).length = g.m + 1 ∧
      ∀ j, j < g.m + 1 → Lit.eval σ ((S.getD i []).getD j 0) =
        decide (j + 1 ≤ ((vals.take (i + 1)).filter id).length)) :
    ∀ c ∈ counterCls g caps S, Clause.eval σ c = true := by
  intro c hc
  have hlen : caps.length = vals.length := fa2_length_eq hl
  have hcl : 0 < caps.length := List.length_pos_iff.mpr hne
  by_cases hm0 : g.m = 0
  · simp only [counterCls, ite_eq_left hm0, List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    rw [clause_eval₁, lit_neg_eval σ x (hz x hx)]
    obtain ⟨vx, hvx, hvxv⟩ := fa2_mem_left hl hx
    rw [hvxv]
    cases vx with
    | false => rfl
    | true =>
        exfalso
        have h1 : 0 < (vals.filter id).length :=
          List.length_pos_of_mem (List.mem_filter.mpr ⟨hvx, by decide⟩)
        omega
  · obtain ⟨hSl, hSr⟩ := hS hm0
    have hSlen : ∀ i, i < caps.length → (S.getD i []).length = g.m + 1 := fun i hi => (hSr i hi).1
    have hSev : ∀ i, i < caps.length → ∀ j, j < g.m + 1 →
        Lit.eval σ ((S.getD i []).getD j 0) = decide (j + 1 ≤ ((vals.take (i + 1)).filter id).length) :=
      fun i hi => (hSr i hi).2
    have htle : ∀ b : Bool, b.toNat ≤ 1 := fun b => by cases b <;> decide
    simp only [counterCls] at hc
    rw [ite_eq_right hm0, List.mem_append] at hc
    rcases hc with hcf | hcs
    · rw [List.mem_flatMap] at hcf
      obtain ⟨i, hir, hci⟩ := hcf
      rw [List.mem_range] at hir
      rw [List.mem_flatMap] at hci
      obtain ⟨j, hjr, hcj⟩ := hci
      rw [List.mem_range] at hjr
      have hiv : i < vals.length := by omega
      have hvi := fa2_getD hl i hir 0 false
      have hxz : caps.getD i 0 ≠ 0 := hz _ (getD_mem _ _ _ hir)
      have hFs : ((vals.take (i + 1)).filter id).length =
          ((vals.take i).filter id).length + (vals.getD i false).toNat := filter_take_succ vals i hiv
      have hFm : ((vals.take i).filter id).length ≤ ((vals.take (i + 1)).filter id).length :=
        cnt_mono' vals (Nat.le_succ i)
      have hRv : ∀ j', j' < g.m + 1 → Lit.eval σ ((S.getD i []).getD j' 0) =
          decide (j' + 1 ≤ ((vals.take (i + 1)).filter id).length) := hSev i hir
      have hrz : (S.getD i []).getD j 0 ≠ 0 :=
        hzS _ (getD_mem _ _ _ (by omega)) _ (getD_mem _ _ _ (by rw [hSlen i hir]; exact hjr))
      by_cases hi0 : i = 0
      · subst hi0
        have hFz : ((vals.take 0).filter id).length = 0 := rfl
        have hF0 : ((vals.take (0 + 1)).filter id).length ≤ 1 := by
          have htle0 := htle (vals.getD 0 false)
          omega
        by_cases hj0 : j = 0
        · subst hj0
          simp only [ite_eq_right (by decide : ¬ (0:Nat) > 0)] at hcj
          simp only [Option.toList, List.nil_append, List.cons_append, List.singleton_append,
            List.mem_append, List.mem_cons, List.mem_singleton, List.mem_nil_iff, false_or, or_false] at hcj
          have hRv0 := hRv 0 (by omega)
          rcases hcj with h | h
          · subst h
            rw [clause_eval₂, lit_neg_eval σ _ hxz, hvi, hRv0]
            cases hv0 : vals.getD 0 false
            · rfl
            · have ht : (vals.getD 0 false).toNat = 1 := by rw [hv0, Bool.toNat_true]
              rw [decide_eq_true (by omega : 0 + 1 ≤ ((vals.take (0 + 1)).filter id).length)]
              rfl
          · subst h
            have hrz0 : (S.getD 0 []).getD 0 0 ≠ 0 := hrz
            rw [clause_eval₂, lit_neg_eval σ _ hrz0, hRv0, hvi]
            cases hv0 : vals.getD 0 false
            · have ht : (vals.getD 0 false).toNat = 0 := by rw [hv0, Bool.toNat_false]
              rw [decide_eq_false (by omega : ¬ 0 + 1 ≤ ((vals.take (0 + 1)).filter id).length)]
              rfl
            · have ht : (vals.getD 0 false).toNat = 1 := by rw [hv0, Bool.toNat_true]
              rw [decide_eq_true (by omega : 0 + 1 ≤ ((vals.take (0 + 1)).filter id).length)]
              rfl
        · have hj0' : j > 0 := Nat.pos_of_ne_zero hj0
          simp only [ite_eq_right (by decide : ¬ (0:Nat) > 0), ite_eq_left hj0'] at hcj
          simp only [Option.toList, List.nil_append, List.cons_append, List.singleton_append,
            List.mem_append, List.mem_cons, List.mem_singleton, List.mem_nil_iff, false_or, or_false] at hcj
          subst hcj
          rw [clause_eval₁, lit_neg_eval σ _ hrz, hRv j hjr,
            decide_eq_false (by omega : ¬ j + 1 ≤ ((vals.take (0 + 1)).filter id).length)]
          rfl
      · have hi0' : i > 0 := Nat.pos_of_ne_zero hi0
        have hPv : ∀ j', j' < g.m + 1 → Lit.eval σ ((S.getD (i - 1) []).getD j' 0) =
            decide (j' + 1 ≤ ((vals.take i).filter id).length) := by
          intro j' hj'
          have h := hSev (i - 1) (by omega) j' hj'
          rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at h
        have hpz : (S.getD (i - 1) []).getD j 0 ≠ 0 :=
          hzS _ (getD_mem _ _ _ (by omega)) _ (getD_mem _ _ _ (by rw [hSlen (i - 1) (by omega)]; exact hjr))
        rw [ite_eq_left hi0'] at hcj
        by_cases hj0 : j = 0
        · subst hj0
          simp only [ite_eq_right (by decide : ¬ (0:Nat) > 0)] at hcj
          simp only [Option.toList, List.nil_append, List.cons_append, List.singleton_append,
            List.mem_append, List.mem_cons, List.mem_singleton, List.mem_nil_iff, false_or, or_false] at hcj
          have hRv0 := hRv 0 (by omega)
          have hPv0 := hPv 0 (by omega)
          rcases hcj with h | h | h
          · subst h
            rw [clause_eval₂, lit_neg_eval σ _ hpz, hPv0, hRv0]
            by_cases hp : 0 + 1 ≤ ((vals.take i).filter id).length
            · rw [decide_eq_true hp, decide_eq_true (Nat.le_trans hp hFm)]
              rfl
            · rw [decide_eq_false hp]
              rfl
          · subst h
            rw [clause_eval₂, lit_neg_eval σ _ hxz, hvi, hRv0]
            cases hvi2 : vals.getD i false
            · rfl
            · have ht : (vals.getD i false).toNat = 1 := by rw [hvi2, Bool.toNat_true]
              rw [decide_eq_true (by omega : 0 + 1 ≤ ((vals.take (i + 1)).filter id).length)]
              rfl
          · subst h
            rw [clause_eval₃, lit_neg_eval σ _ hrz, hRv0, hPv0, hvi]
            by_cases hp : 0 + 1 ≤ ((vals.take (i + 1)).filter id).length
            · rw [decide_eq_true hp]
              by_cases hq : 0 + 1 ≤ ((vals.take i).filter id).length
              · rw [decide_eq_true hq]
                rfl
              · cases hvi2 : vals.getD i false
                · exfalso
                  have ht : (vals.getD i false).toNat = 0 := by rw [hvi2, Bool.toNat_false]
                  omega
                · rw [decide_eq_false hq]
                  rfl
            · rw [decide_eq_false hp]
              rfl
        · have hj0' : j > 0 := Nat.pos_of_ne_zero hj0
          simp only [ite_eq_left hi0', ite_eq_left hj0'] at hcj
          simp only [Option.toList, List.nil_append, List.cons_append, List.singleton_append,
            List.mem_append, List.mem_cons, List.mem_singleton, List.mem_nil_iff, false_or, or_false] at hcj
          have hRvj := hRv j hjr
          have hPvj := hPv j hjr
          have hPvm := hPv (j - 1) (by omega)
          have hpzm : (S.getD (i - 1) []).getD (j - 1) 0 ≠ 0 :=
            hzS _ (getD_mem _ _ _ (by omega)) _ (getD_mem _ _ _ (by rw [hSlen (i - 1) (by omega)]; omega))
          rcases hcj with h | h | h | h
          · subst h
            rw [clause_eval₂, lit_neg_eval σ _ hpz, hPvj, hRvj]
            by_cases hp : j + 1 ≤ ((vals.take i).filter id).length
            · rw [decide_eq_true hp, decide_eq_true (Nat.le_trans hp hFm)]
              rfl
            · rw [decide_eq_false hp]
              rfl
          · subst h
            rw [clause_eval₃, lit_neg_eval σ _ hxz, lit_neg_eval σ _ hpzm, hvi, hPvm, hRvj]
            cases hvi2 : vals.getD i false
            · rfl
            · have ht : (vals.getD i false).toNat = 1 := by rw [hvi2, Bool.toNat_true]
              by_cases hq : j - 1 + 1 ≤ ((vals.take i).filter id).length
              · rw [decide_eq_true hq,
                  decide_eq_true (by omega : j + 1 ≤ ((vals.take (i + 1)).filter id).length)]
                rfl
              · rw [decide_eq_false hq]
                rfl
          · subst h
            rw [clause_eval₃, lit_neg_eval σ _ hrz, hRvj, hPvj, hvi]
            by_cases hp : j + 1 ≤ ((vals.take (i + 1)).filter id).length
            · rw [decide_eq_true hp]
              by_cases hq : j + 1 ≤ ((vals.take i).filter id).length
              · rw [decide_eq_true hq]
                rfl
              · cases hvi2 : vals.getD i false
                · exfalso
                  have ht : (vals.getD i false).toNat = 0 := by rw [hvi2, Bool.toNat_false]
                  omega
                · rw [decide_eq_false hq]
                  rfl
            · rw [decide_eq_false hp]
              rfl
          · subst h
            rw [clause_eval₃, lit_neg_eval σ _ hrz, hRvj, hPvj, hPvm]
            by_cases hp : j + 1 ≤ ((vals.take (i + 1)).filter id).length
            · rw [decide_eq_true hp]
              by_cases hq : j + 1 ≤ ((vals.take i).filter id).length
              · rw [decide_eq_true hq]
                rfl
              · rw [decide_eq_false hq]
                by_cases hq2 : j - 1 + 1 ≤ ((vals.take i).filter id).length
                · rw [decide_eq_true hq2]
                  rfl
                · exfalso
                  have htle1 := htle (vals.getD i false)
                  omega
            · rw [decide_eq_false hp]
              rfl
    · rw [List.mem_singleton] at hcs
      subst hcs
      have hzX : (S.getD (caps.length - 1) []).getD g.m 0 ≠ 0 :=
        hzS _ (getD_mem _ _ _ (by omega)) _ (getD_mem _ _ _ (by rw [hSlen (caps.length - 1) (by omega)]; omega))
      have hev := hSev (caps.length - 1) (by omega) g.m (Nat.lt_succ_self g.m)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ caps.length)] at hev
      have hfl : (vals.take caps.length).filter id = vals.filter id := by rw [hlen, List.take_length]
      rw [clause_eval₁, lit_neg_eval σ _ hzX, hev,
        decide_eq_false (show ¬ g.m + 1 ≤ ((vals.take caps.length).filter id).length by rw [hfl]; omega)]
      rfl


section Bridge

def btwCheck : Bool := allSq.all fun a => allSq.all fun b =>
  (btw a.val b.val).all (· < 64) && allSq.all fun z => (btw a.val b.val).contains z.val == inSeg a b z

set_option maxRecDepth 100000 in
theorem btwCheck_true : btwCheck = true := by decide +kernel

theorem btw_lt (a b : Sq) (z : Nat) (hz : z ∈ btw a.val b.val) : z < 64 := by
  have h := btwCheck_true
  simp only [btwCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h a (mem_allSq a) b (mem_allSq b)).1 z hz

theorem mem_btw_iff (a b z : Sq) : z.val ∈ btw a.val b.val ↔ inSeg a b z = true := by
  have h := btwCheck_true
  simp only [btwCheck, List.all_eq_true, Bool.and_eq_true] at h
  have := (h a (mem_allSq a) b (mem_allSq b)).2 z (mem_allSq z)
  rw [beq_iff_eq] at this
  rw [← this, List.contains_iff_mem]

theorem mem_btw_iff_nat (a b : Sq) (z : Nat) : z ∈ btw a.val b.val ↔ z < 64 ∧ inSeg a b (toSq z) = true := by
  constructor
  · intro hz
    have h64 := btw_lt a b z hz
    refine ⟨h64, (mem_btw_iff a b (toSq z)).mp ?_⟩
    simpa [toSq, Nat.mod_eq_of_lt h64] using hz
  · rintro ⟨h64, hs⟩
    have := (mem_btw_iff a b (toSq z)).mpr hs
    simpa [toSq, Nat.mod_eq_of_lt h64] using this

def kinds5 : List Kind := [.pawn, .knight, .bishop, .rook, .queen]

def geomCheck : Bool := [Color.white, .black].all fun c => kinds5.all fun k => allSq.all fun s => allSq.all fun t =>
  attacksGeom (kindIdx k) (colIdx c) s.val t.val == geomAttack c k s t

set_option maxRecDepth 100000 in
theorem geomCheck_true : geomCheck = true := by decide +kernel

theorem attacksGeom_eq (q : Piece) (hq : q.kind ≠ .king) (s t : Sq) :
    attacksGeom (kindIdx q.kind) (colIdx q.color) s.val t.val = geomAttack q.color q.kind s t := by
  have h := geomCheck_true
  simp only [geomCheck, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨c, k⟩ := q
  exact h c (by cases c <;> simp) k (by cases k <;> simp_all [kinds5]) s (mem_allSq s) t (mem_allSq t)

theorem onb_sqOf (f r : Int) (h : onb f r = true) :
    sqOf f r < 64 ∧ fl (sqOf f r) = f ∧ rk (sqOf f r) = r := by
  simp only [onb, Bool.and_eq_true, decide_eq_true_eq] at h
  have hfe : (↑f.toNat : Int) = f := Int.toNat_of_nonneg (by omega)
  have hre : (↑r.toNat : Int) = r := Int.toNat_of_nonneg (by omega)
  rw [← hfe, ← hre]
  simp only [sqOf, fl, rk]
  omega

theorem fl_rk_sqOf (s : Nat) : sqOf (fl s) (rk s) = s := by
  have h : (fl s + 8 * rk s : Int) = (s : Int) := by
    simp only [fl, rk]; omega
  rw [sqOf, h]; exact Int.toNat_natCast s

theorem ray_eq_go (g : Cfg) (x : Nat) (d : Int × Int) :
    g.ray x d = Cfg.ray.go d (g.K (1 - x)) 8 (fl (g.K x) + d.1) (rk (g.K x) + d.2) := rfl

theorem go_getD (d : Int × Int) (o : Nat) :
    ∀ (fuel : Nat) (f r : Int) (j : Nat), j < (Cfg.ray.go d o fuel f r).length →
    (Cfg.ray.go d o fuel f r).getD j 0 < 64 ∧
      fl ((Cfg.ray.go d o fuel f r).getD j 0) = f + (j : Int) * d.1 ∧
      rk ((Cfg.ray.go d o fuel f r).getD j 0) = r + (j : Int) * d.2 := by
  intro fuel
  induction fuel with
  | zero => intro f r j hj; rw [Cfg.ray.go.eq_1] at hj; simp at hj
  | succ fuel ih =>
    intro f r j hj
    rw [Cfg.ray.go.eq_2] at hj ⊢
    by_cases hb : onb f r = true
    · rw [if_pos hb] at hj ⊢
      by_cases hsq : sqOf f r = o
      · rw [if_pos hsq] at hj; simp at hj
      · rw [if_neg hsq] at hj ⊢
        cases j with
        | zero =>
          rw [List.getD_cons_zero]
          obtain ⟨hlt, hf, hr⟩ := onb_sqOf f r hb
          refine ⟨hlt, by rw [hf]; omega, by rw [hr]; omega⟩
        | succ j' =>
          rw [List.length_cons] at hj
          rw [List.getD_cons_succ]
          obtain ⟨hlt, hf, hr⟩ := ih (f + d.1) (r + d.2) j' (by omega)
          have hcast : ((↑(j' + 1) : Int)) = ↑j' + 1 := by omega
          refine ⟨hlt, ?_, ?_⟩
          · rw [hf, hcast, Int.add_mul, Int.one_mul]; omega
          · rw [hr, hcast, Int.add_mul, Int.one_mul]; omega
    · rw [if_neg hb] at hj; simp at hj

theorem go_ne_o (d : Int × Int) (o : Nat) :
    ∀ (fuel : Nat) (f r : Int) (s : Nat), s ∈ Cfg.ray.go d o fuel f r → s ≠ o := by
  intro fuel
  induction fuel with
  | zero => intro f r s hs; rw [Cfg.ray.go.eq_1] at hs; simp at hs
  | succ fuel ih =>
    intro f r s hs
    rw [Cfg.ray.go.eq_2] at hs
    by_cases hb : onb f r = true
    · rw [if_pos hb] at hs
      by_cases hsq : sqOf f r = o
      · rw [if_pos hsq] at hs; simp at hs
      · rw [if_neg hsq] at hs
        rcases List.mem_cons.mp hs with h | h
        · exact h.symm ▸ hsq
        · exact ih _ _ _ h
    · rw [if_neg hb] at hs; simp at hs

theorem take_map_getD : ∀ (l : List Nat) (j : Nat), j ≤ l.length →
    l.take j = (List.range j).map fun i => l.getD i 0 := by
  intro l
  induction l with
  | nil => intro j hj; simp only [List.length_nil, Nat.le_zero] at hj; subst hj; rfl
  | cons a as ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ j =>
      rw [List.take_succ_cons]
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp]
      rw [List.getD_cons_zero]
      congr 1
      rw [List.length_cons] at hj
      rw [ih j (by omega)]
      apply List.map_congr_left
      intro i _
      exact List.getD_cons_succ.symm

theorem sign_kd (k : Nat) (hk : 1 ≤ k) (d1 : Int) (hd1 : d1 = -1 ∨ d1 = 0 ∨ d1 = 1) :
    Int.sign (↑k * d1) = d1 := by
  rcases hd1 with rfl | rfl | rfl
  · rw [Int.mul_neg, Int.mul_one, Int.sign_neg]; cases k with | zero => omega | succ k => rfl
  · rw [Int.mul_zero]; rfl
  · rw [Int.mul_one]; cases k with | zero => omega | succ k => rfl

theorem toSq_val (s : Sq) : toSq s.val = s := Fin.ext (Nat.mod_eq_of_lt s.isLt)

theorem raySquares_eq (g : Cfg) (x : Nat) : g.raySquares x = (orth ++ diag).flatMap (g.ray x) := rfl

theorem fx_sq (s : Sq) : fx s = fl s.val := rfl

theorem ry_sq (s : Sq) : ry s = rk s.val := rfl


theorem fx_toSq (n : Nat) (h : n < 64) : fx (toSq n) = fl n := by
  simp only [fx, fl, toSq, Sq.file]
  congr 1
  omega

theorem ry_toSq (n : Nat) (h : n < 64) : ry (toSq n) = rk n := by
  simp only [ry, rk, toSq, Sq.rank]
  congr 1
  omega

theorem toSq_inj (a b : Nat) (ha : a < 64) (hb : b < 64)
    (hf : fx (toSq a) = fx (toSq b)) (hr : ry (toSq a) = ry (toSq b)) : a = b := by
  rw [fx_toSq a ha, fx_toSq b hb] at hf
  rw [ry_toSq a ha, ry_toSq b hb] at hr
  simp only [fl, rk] at hf hr
  omega

theorem mul4 (a b c e : Int) : (a * b) * (c * e) = (a * c) * (b * e) := by
  rw [Int.mul_assoc, Int.mul_left_comm b c, ← Int.mul_assoc]

theorem mul_cancel_l {c A B : Int} (hc : c ≠ 0) (h : c * A = c * B) : A = B := by
  have : c * (A - B) = 0 := by rw [Int.mul_sub]; omega
  rcases Int.mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hc
  · omega

theorem mul_cancel_r {A B c : Int} (hc : c ≠ 0) (h : A * c = B * c) : A = B := by
  have : (A - B) * c = 0 := by rw [Int.sub_mul]; omega
  rcases Int.mul_eq_zero.mp this with h1 | h1
  · omega
  · exact absurd h1 hc

theorem natAbs_mul_max_eq (d1 d2 : Int) (hd1 : d1 = -1 ∨ d1 = 0 ∨ d1 = 1) (hd2 : d2 = -1 ∨ d2 = 0 ∨ d2 = 1)
    (hne : d1 ≠ 0 ∨ d2 ≠ 0) (n : Nat) : max (n * d1.natAbs) (n * d2.natAbs) = n := by
  rcases hne with h1n | h2n
  · have ha : d1.natAbs = 1 := by
      rcases hd1 with rfl | rfl | rfl
      · decide
      · exact absurd rfl h1n
      · decide
    have hb2 : d2.natAbs ≤ 1 := by rcases hd2 with rfl | rfl | rfl <;> decide
    have hb' : n * d2.natAbs ≤ n := by
      have hle := Nat.mul_le_mul_left n hb2
      rwa [Nat.mul_one] at hle
    rw [ha, Nat.mul_one]
    exact Nat.max_eq_left hb'
  · have ha : d2.natAbs = 1 := by
      rcases hd2 with rfl | rfl | rfl
      · decide
      · exact absurd rfl h2n
      · decide
    have hb1 : d1.natAbs ≤ 1 := by rcases hd1 with rfl | rfl | rfl <;> decide
    have hb' : n * d1.natAbs ≤ n := by
      have hle := Nat.mul_le_mul_left n hb1
      rwa [Nat.mul_one] at hle
    rw [ha, Nat.mul_one]
    exact Nat.max_eq_right hb'

theorem mem_orth_diag_fst (d : Int × Int) (hd : d ∈ orth ++ diag) : d.1 = -1 ∨ d.1 = 0 ∨ d.1 = 1 := by
  simp only [orth, diag, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with (h | h | h | h) | (h | h | h | h) <;> rw [h] <;> decide

theorem mem_orth_diag_snd (d : Int × Int) (hd : d ∈ orth ++ diag) : d.2 = -1 ∨ d.2 = 0 ∨ d.2 = 1 := by
  simp only [orth, diag, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with (h | h | h | h) | (h | h | h | h) <;> rw [h] <;> decide

theorem mem_orth_diag_ne (d : Int × Int) (hd : d ∈ orth ++ diag) : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
  simp only [orth, diag, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with (h | h | h | h) | (h | h | h | h) <;> rw [h] <;> decide

theorem ray_getD (g : Cfg) (x : Nat) (d : Int × Int) (hd : d ∈ orth ++ diag) (hK : g.K x < 64) (j : Nat)
    (hj : j < (g.ray x d).length) :
    (g.ray x d).getD j 0 < 64 ∧ fl ((g.ray x d).getD j 0) = fl (g.K x) + ((j : Int) + 1) * d.1 ∧
      rk ((g.ray x d).getD j 0) = rk (g.K x) + ((j : Int) + 1) * d.2 := by
  rw [ray_eq_go] at hj ⊢
  obtain ⟨h1, h2, h3⟩ := go_getD d (g.K (1 - x)) 8 _ _ j hj
  refine ⟨h1, ?_, ?_⟩
  · rw [h2, Int.add_mul, Int.one_mul]; omega
  · rw [h3, Int.add_mul, Int.one_mul]; omega

theorem between_ray (K b : Nat) (k : Nat) (hk : 1 ≤ k) (d1 d2 : Int)
    (hd1 : d1 = -1 ∨ d1 = 0 ∨ d1 = 1) (hd2 : d2 = -1 ∨ d2 = 0 ∨ d2 = 1) (hne : d1 ≠ 0 ∨ d2 ≠ 0)
    (hf : fl b = fl K + ↑k * d1) (hr : rk b = rk K + ↑k * d2) :
    between K b = some ((List.range (k - 1)).map fun (i : Nat) => sqOf (fl K + d1 * ((i : Int) + 1)) (rk K + d2 * ((i : Int) + 1))) := by
  have hdf : fl b - fl K = ↑k * d1 := by omega
  have hdr : rk b - rk K = ↑k * d2 := by omega
  have hs1 := sign_kd k hk d1 hd1
  have hs2 := sign_kd k hk d2 hd2
  simp only [between, hdf, hdr, hs1, hs2, Int.natAbs_mul, Int.natAbs_natCast]
  rcases hd1 with rfl | rfl | rfl <;> rcases hd2 with rfl | rfl | rfl
  · simp only [show (-1:Int).natAbs = 1 from rfl]
    rw [if_neg (by omega), if_neg (by omega), show max (k * 1) (k * 1) = k from by omega]
  · simp only [show (-1:Int).natAbs = 1 from rfl, show (0:Int).natAbs = 0 from rfl]
    rw [if_neg (by omega), if_neg (by omega), show max (k * 1) (k * 0) = k from by omega]
  · simp only [show (-1:Int).natAbs = 1 from rfl, show (1:Int).natAbs = 1 from rfl]
    rw [if_neg (by omega), if_neg (by omega), show max (k * 1) (k * 1) = k from by omega]
  · simp only [show (0:Int).natAbs = 0 from rfl, show (-1:Int).natAbs = 1 from rfl]
    rw [if_neg (by omega), if_neg (by omega), show max (k * 0) (k * 1) = k from by omega]
  · rcases hne with h | h <;> exact absurd rfl h
  · simp only [show (0:Int).natAbs = 0 from rfl, show (1:Int).natAbs = 1 from rfl]
    rw [if_neg (by omega), if_neg (by omega), show max (k * 0) (k * 1) = k from by omega]
  · simp only [show (1:Int).natAbs = 1 from rfl, show (-1:Int).natAbs = 1 from rfl]
    rw [if_neg (by omega), if_neg (by omega), show max (k * 1) (k * 1) = k from by omega]
  · simp only [show (1:Int).natAbs = 1 from rfl, show (0:Int).natAbs = 0 from rfl]
    rw [if_neg (by omega), if_neg (by omega), show max (k * 1) (k * 0) = k from by omega]
  · simp only [show (1:Int).natAbs = 1 from rfl]
    rw [if_neg (by omega), if_neg (by omega), show max (k * 1) (k * 1) = k from by omega]

theorem ray_take_btw (g : Cfg) (x : Nat) (d : Int × Int) (hd : d ∈ orth ++ diag) (hK : g.K x < 64) (j : Nat)
    (hj : j < (g.ray x d).length) : (g.ray x d).take j = btw (g.K x) ((g.ray x d).getD j 0) := by
  obtain ⟨b64, hf, hr⟩ := ray_getD g x d hd hK j hj
  have hcast : (↑(j + 1) : Int) = ↑j + 1 := by omega
  have hf' : fl ((g.ray x d).getD j 0) = fl (g.K x) + (↑(j + 1) : Int) * d.1 := by rw [hcast]; exact hf
  have hr' : rk ((g.ray x d).getD j 0) = rk (g.K x) + (↑(j + 1) : Int) * d.2 := by rw [hcast]; exact hr
  have hbet := between_ray (g.K x) ((g.ray x d).getD j 0) (j + 1) (by omega) d.1 d.2
    (mem_orth_diag_fst d hd) (mem_orth_diag_snd d hd) (mem_orth_diag_ne d hd) hf' hr'
  rw [show j + 1 - 1 = j from by omega] at hbet
  have htake : (g.ray x d).take j = (List.range j).map fun i => (g.ray x d).getD i 0 :=
    take_map_getD _ _ (by omega)
  rw [htake]
  simp only [btw, hbet, Option.getD_some]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  obtain ⟨i64, hfi, hri⟩ := ray_getD g x d hd hK i (by omega)
  rw [← fl_rk_sqOf ((g.ray x d).getD i 0), hfi, hri, Int.mul_comm (↑i + 1) d.1, Int.mul_comm (↑i + 1) d.2]

theorem ray_inSeg_intro (K s' Ko : Nat) (hK : K < 64) (hs' : s' < 64) (hKo : Ko < 64)
    (d1 d2 : Int) (hd1 : d1 = -1 ∨ d1 = 0 ∨ d1 = 1) (hd2 : d2 = -1 ∨ d2 = 0 ∨ d2 = 1) (hne : d1 ≠ 0 ∨ d2 ≠ 0)
    (k m : Nat) (hm1 : 1 ≤ m) (hmk : m < k)
    (hfk : fl s' - fl K = ↑k * d1) (hrk : rk s' - rk K = ↑k * d2)
    (hfm : fl Ko - fl K = ↑m * d1) (hrm : rk Ko - rk K = ↑m * d2)
    (hal : aligned (toSq K) (toSq s') = true) :
    inSeg (toSq K) (toSq s') (toSq Ko) = true := by
  have bfxK : fx (toSq K) = fl K := fx_toSq K hK
  have brkK : ry (toSq K) = rk K := ry_toSq K hK
  have bfxs : fx (toSq s') = fl s' := fx_toSq s' hs'
  have brys : ry (toSq s') = rk s' := ry_toSq s' hs'
  have bfxKo : fx (toSq Ko) = fl Ko := fx_toSq Ko hKo
  have brkKo : ry (toSq Ko) = rk Ko := ry_toSq Ko hKo
  have eF1 : fx (toSq K) - fx (toSq Ko) = -(↑m * d1) := by rw [bfxK, bfxKo]; omega
  have eR1 : ry (toSq K) - ry (toSq Ko) = -(↑m * d2) := by rw [brkK, brkKo]; omega
  have eF2 : fx (toSq Ko) - fx (toSq s') = (↑m - ↑k) * d1 := by
    rw [bfxKo, bfxs, Int.sub_mul]; omega
  have eR2 : ry (toSq Ko) - ry (toSq s') = (↑m - ↑k) * d2 := by
    rw [brkKo, brys, Int.sub_mul]; omega
  have eF3 : fx (toSq K) - fx (toSq s') = -(↑k * d1) := by rw [bfxK, bfxs]; omega
  have eR3 : ry (toSq K) - ry (toSq s') = -(↑k * d2) := by rw [brkK, brys]; omega
  have nmk : ((↑m : Int)).natAbs = m := Int.natAbs_natCast m
  have nkk : ((↑k : Int)).natAbs = k := Int.natAbs_natCast k
  have nneg : ((↑m - ↑k : Int)).natAbs = k - m := by
    have e : (↑m - ↑k : Int) = -↑(k - m) := by omega
    rw [e, Int.natAbs_neg, Int.natAbs_natCast]
  simp only [inSeg, onLine, collinear, kdist, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  refine ⟨⟨⟨⟨hal, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [bfxKo, brys, brkK, brkKo, bfxs, bfxK]
    rw [hfm, hrk, hrm, hfk]
    rw [mul4, mul4 (↑m) d2 (↑k) d1, Int.mul_comm d2 d1]
  · intro h
    rcases hne with h1n | h2n
    · have e := congrArg fx h
      rw [bfxKo, bfxK] at e
      have e0 : (↑m : Int) * d1 = 0 := by omega
      rcases Int.mul_eq_zero.mp e0 with hm0 | hd0
      · omega
      · exact absurd hd0 h1n
    · have e := congrArg ry h
      rw [brkKo, brkK] at e
      have e0 : (↑m : Int) * d2 = 0 := by omega
      rcases Int.mul_eq_zero.mp e0 with hm0 | hd0
      · omega
      · exact absurd hd0 h2n
  · intro h
    rcases hne with h1n | h2n
    · have e := congrArg fx h
      rw [bfxKo, bfxs] at e
      have e0 : (↑m : Int) * d1 = ↑k * d1 := by omega
      have := mul_cancel_r h1n e0
      omega
    · have e := congrArg ry h
      rw [brkKo, brys] at e
      have e0 : (↑m : Int) * d2 = ↑k * d2 := by omega
      have := mul_cancel_r h2n e0
      omega
  · rw [eF1, eR1, eF2, eR2, eF3, eR3]
    simp only [Int.natAbs_neg, Int.natAbs_mul, nmk, nkk, nneg, natAbs_mul_max_eq d1 d2 hd1 hd2 hne]
    omega

theorem go_len_of_ok (d : Int × Int) (o : Nat) :
    ∀ (fuel : Nat) (f r : Int) (M : Nat),
    (∀ m, m < M → onb (f + (m : Int) * d.1) (r + (m : Int) * d.2) = true ∧
      sqOf (f + (m : Int) * d.1) (r + (m : Int) * d.2) ≠ o) →
    ∀ j, j < min fuel M → j < (Cfg.ray.go d o fuel f r).length ∧
      (Cfg.ray.go d o fuel f r).getD j 0 = sqOf (f + (j : Int) * d.1) (r + (j : Int) * d.2) := by
  intro fuel
  induction fuel with
  | zero => intro f r M hok j hj; simp at hj
  | succ fuel ih =>
    intro f r M hok j hj
    have hM : 0 < M := by omega
    have e10 : f + ((0 : Nat) : Int) * d.1 = f := by omega
    have e20 : r + ((0 : Nat) : Int) * d.2 = r := by omega
    have hb : onb f r = true := by
      have h := (hok 0 hM).1; rwa [e10, e20] at h
    have hsq0 : sqOf f r ≠ o := by
      have h := (hok 0 hM).2; rwa [e10, e20] at h
    rw [Cfg.ray.go.eq_2]
    rw [if_pos hb, if_neg hsq0]
    cases j with
    | zero =>
      simp only [List.length_cons, List.getD_cons_zero]
      refine ⟨by omega, ?_⟩
      congr 1 <;> omega
    | succ j' =>
      have hj' : j' < min fuel (M - 1) := by omega
      have hok' : ∀ m, m < M - 1 →
          onb (f + d.1 + (m : Int) * d.1) (r + d.2 + (m : Int) * d.2) = true ∧
          sqOf (f + d.1 + (m : Int) * d.1) (r + d.2 + (m : Int) * d.2) ≠ o := by
        intro m hm
        have h1 := hok (m + 1) (by omega)
        have e1 : f + d.1 + (↑m : Int) * d.1 = f + (↑(m + 1) : Int) * d.1 := by
          rw [show (↑(m + 1) : Int) = ↑m + 1 from by omega, Int.add_mul, Int.one_mul]; omega
        have e2 : r + d.2 + (↑m : Int) * d.2 = r + (↑(m + 1) : Int) * d.2 := by
          rw [show (↑(m + 1) : Int) = ↑m + 1 from by omega, Int.add_mul, Int.one_mul]; omega
        rw [← e1, ← e2] at h1
        exact h1
      obtain ⟨hlt, heq⟩ := ih (f + d.1) (r + d.2) (M - 1) hok' j' hj'
      refine ⟨by rw [List.length_cons]; omega, ?_⟩
      rw [List.getD_cons_succ, heq]
      have e1 : f + (↑(j' + 1) : Int) * d.1 = f + d.1 + (↑j' : Int) * d.1 := by
        rw [show (↑(j' + 1) : Int) = ↑j' + 1 from by omega, Int.add_mul, Int.one_mul]; omega
      have e2 : r + (↑(j' + 1) : Int) * d.2 = r + d.2 + (↑j' : Int) * d.2 := by
        rw [show (↑(j' + 1) : Int) = ↑j' + 1 from by omega, Int.add_mul, Int.one_mul]; omega
      rw [e1, e2]

theorem ray_elim_tail (K s' Ko : Nat) (hK : K < 64) (hs' : s' < 64) (hKo : Ko < 64)
    (d1 d2 : Int) (hd1 : d1 = -1 ∨ d1 = 0 ∨ d1 = 1) (hd2 : d2 = -1 ∨ d2 = 0 ∨ d2 = 1) (hne : d1 ≠ 0 ∨ d2 ≠ 0)
    (j : Nat) (M : Int)
    (hΔf' : fl Ko - fl K = M * d1) (hΔr' : rk Ko - rk K = M * d2)
    (hfk : fl s' - fl K = (↑j + 1) * d1) (hrk : rk s' - rk K = (↑j + 1) * d2)
    (hza' : toSq Ko ≠ toSq K) (hzb' : toSq Ko ≠ toSq s')
    (hkd : kdist (toSq K) (toSq Ko) + kdist (toSq Ko) (toSq s') = kdist (toSq K) (toSq s')) :
    ∃ m : Nat, 1 ≤ m ∧ m ≤ j ∧ fl Ko - fl K = ↑m * d1 ∧ rk Ko - rk K = ↑m * d2 := by
  have e1 : fx (toSq K) - fx (toSq Ko) = -(M * d1) := by rw [fx_toSq K hK, fx_toSq Ko hKo]; omega
  have e2 : ry (toSq K) - ry (toSq Ko) = -(M * d2) := by rw [ry_toSq K hK, ry_toSq Ko hKo]; omega
  have e3 : fx (toSq Ko) - fx (toSq s') = (M - (↑j + 1)) * d1 := by
    rw [fx_toSq Ko hKo, fx_toSq s' hs', Int.sub_mul]; omega
  have e4 : ry (toSq Ko) - ry (toSq s') = (M - (↑j + 1)) * d2 := by
    rw [ry_toSq Ko hKo, ry_toSq s' hs', Int.sub_mul]; omega
  have e5 : fx (toSq K) - fx (toSq s') = -((↑j + 1) * d1) := by
    rw [fx_toSq K hK, fx_toSq s' hs']; omega
  have e6 : ry (toSq K) - ry (toSq s') = -((↑j + 1) * d2) := by
    rw [ry_toSq K hK, ry_toSq s' hs']; omega
  simp only [kdist, e1, e2, e3, e4, e5, e6] at hkd
  simp only [Int.natAbs_neg, Int.natAbs_mul,
    show ((↑j + 1 : Int)).natAbs = j + 1 from by
      rw [show (↑j + 1 : Int) = ↑(j + 1) from by omega, Int.natAbs_natCast]] at hkd
  rw [natAbs_mul_max_eq d1 d2 hd1 hd2 hne M.natAbs, natAbs_mul_max_eq d1 d2 hd1 hd2 hne (M - (↑j + 1)).natAbs,
    natAbs_mul_max_eq d1 d2 hd1 hd2 hne (j + 1)] at hkd
  have hM0 : 0 ≤ M := by omega
  have hMne0 : M ≠ 0 := by
    intro hM
    have hfl : fl Ko - fl K = 0 := by rw [hM, Int.zero_mul] at hΔf'; exact hΔf'
    have hrk2 : rk Ko - rk K = 0 := by rw [hM, Int.zero_mul] at hΔr'; exact hΔr'
    exact hza' (congrArg toSq (toSq_inj Ko K hKo hK
      (by rw [fx_toSq Ko hKo, fx_toSq K hK]; omega) (by rw [ry_toSq Ko hKo, ry_toSq K hK]; omega)))
  have hMne : M ≠ ↑j + 1 := by
    intro hM
    rw [hM] at hΔf' hΔr'
    exact hzb' (congrArg toSq (toSq_inj Ko s' hKo hs'
      (by rw [fx_toSq Ko hKo, fx_toSq s' hs']; omega) (by rw [ry_toSq Ko hKo, ry_toSq s' hs']; omega)))
  refine ⟨M.toNat, by omega, by omega, ?_, ?_⟩
  · rw [show (↑M.toNat : Int) = M from Int.toNat_of_nonneg hM0]; exact hΔf'
  · rw [show (↑M.toNat : Int) = M from Int.toNat_of_nonneg hM0]; exact hΔr'

theorem ray_inSeg_elim (K s' Ko : Nat) (hK : K < 64) (hs' : s' < 64) (hKo : Ko < 64)
    (d1 d2 : Int) (hd1 : d1 = -1 ∨ d1 = 0 ∨ d1 = 1) (hd2 : d2 = -1 ∨ d2 = 0 ∨ d2 = 1) (hne : d1 ≠ 0 ∨ d2 ≠ 0)
    (j : Nat)
    (hfk : fl s' - fl K = (↑j + 1) * d1) (hrk : rk s' - rk K = (↑j + 1) * d2)
    (hins : inSeg (toSq K) (toSq s') (toSq Ko) = true) :
    ∃ m : Nat, 1 ≤ m ∧ m ≤ j ∧ fl Ko - fl K = ↑m * d1 ∧ rk Ko - rk K = ↑m * d2 := by
  simp only [inSeg, onLine, collinear, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hins
  obtain ⟨⟨⟨⟨_, hcol⟩, hza'⟩, hzb'⟩, hkd⟩ := hins
  rw [fx_toSq Ko hKo, ry_toSq s' hs', ry_toSq K hK, ry_toSq Ko hKo, fx_toSq s' hs', fx_toSq K hK] at hcol
  rw [hrk, hfk] at hcol
  have hne0 : (↑j + 1 : Int) ≠ 0 := by omega
  rw [Int.mul_left_comm _ (↑j + 1) d2, Int.mul_left_comm _ (↑j + 1) d1] at hcol
  have H : (fl Ko - fl K) * d2 = (rk Ko - rk K) * d1 := mul_cancel_l hne0 hcol
  by_cases h01 : d1 = 0
  · subst h01
    have hd2n : d2 ≠ 0 := by
      rcases hne with h | h
      · exact absurd rfl h
      · exact h
    rw [Int.mul_zero] at H
    have hΔf0 : fl Ko - fl K = 0 := by
      rcases Int.mul_eq_zero.mp H with h | h
      · exact h
      · exact absurd h hd2n
    have hd22 : d2 * d2 = 1 := by
      rcases hd2 with rfl | rfl | rfl
      · decide
      · exact absurd rfl hd2n
      · decide
    refine ray_elim_tail K s' Ko hK hs' hKo 0 d2 (by decide) hd2 (Or.inr hd2n) j ((rk Ko - rk K) * d2)
      ?_ ?_ hfk hrk hza' hzb' hkd
    · rw [Int.mul_zero]; exact hΔf0
    · rw [Int.mul_assoc, hd22, Int.mul_one]
  · by_cases h02 : d2 = 0
    · subst h02
      rw [Int.mul_zero] at H
      have hΔr0 : rk Ko - rk K = 0 := by
        rcases Int.mul_eq_zero.mp H.symm with h | h
        · exact h
        · exact absurd h h01
      have hd11 : d1 * d1 = 1 := by
        rcases hd1 with rfl | rfl | rfl
        · decide
        · exact absurd rfl h01
        · decide
      refine ray_elim_tail K s' Ko hK hs' hKo d1 0 hd1 (by decide) (by exact hne) j ((fl Ko - fl K) * d1)
        ?_ ?_ hfk hrk hza' hzb' hkd
      · rw [Int.mul_assoc, hd11, Int.mul_one]
      · rw [Int.mul_zero]; exact hΔr0
    · have hd11 : d1 * d1 = 1 := by
        rcases hd1 with rfl | rfl | rfl
        · decide
        · exact absurd rfl h01
        · decide
      have hd22 : d2 * d2 = 1 := by
        rcases hd2 with rfl | rfl | rfl
        · decide
        · exact absurd rfl h02
        · decide
      refine ray_elim_tail K s' Ko hK hs' hKo d1 d2 hd1 hd2 (by exact hne) j ((fl Ko - fl K) * d1)
        ?_ ?_ hfk hrk hza' hzb' hkd
      · rw [Int.mul_assoc, hd11, Int.mul_one]
      · calc rk Ko - rk K = (rk Ko - rk K) * (d1 * d1) := by rw [hd11, Int.mul_one]
          _ = ((rk Ko - rk K) * d1) * d1 := (Int.mul_assoc _ _ _).symm
          _ = ((fl Ko - fl K) * d2) * d1 := by rw [← H]
          _ = (fl Ko - fl K) * (d2 * d1) := Int.mul_assoc _ _ _
          _ = (fl Ko - fl K) * (d1 * d2) := by rw [Int.mul_comm d2 d1]
          _ = ((fl Ko - fl K) * d1) * d2 := (Int.mul_assoc _ _ _).symm

theorem mem_ray_of_dir (g : Cfg) (x : Nat) (hK : g.K x < 64) (hKo : g.K (1 - x) < 64) (s : Sq)
    (d1 d2 : Int) (hd : (d1, d2) ∈ orth ++ diag) (k : Nat) (hk1 : 1 ≤ k)
    (hfk : fl s.val = fl (g.K x) + ↑k * d1) (hrk : rk s.val = rk (g.K x) + ↑k * d2)
    (hns : s ≠ toSq (g.K (1 - x))) (hins : inSeg (toSq (g.K x)) s (toSq (g.K (1 - x))) = false)
    (halt : aligned (toSq (g.K x)) s = true) :
    s.val ∈ g.raySquares x := by
  rw [← toSq_val s] at hns hins halt
  have hfk' : fl s.val - fl (g.K x) = ↑k * d1 := by omega
  have hrk' : rk s.val - rk (g.K x) = ↑k * d2 := by omega
  have hflt : (0 : Int) ≤ fl (g.K x) ∧ fl (g.K x) < 8 := by simp only [fl]; omega
  have hrkt : (0 : Int) ≤ rk (g.K x) ∧ rk (g.K x) < 8 := by simp only [rk]; omega
  have hfls : (0 : Int) ≤ fl s.val ∧ fl s.val < 8 := by simp only [fl]; omega
  have hrks : (0 : Int) ≤ rk s.val ∧ rk s.val < 8 := by simp only [rk]; omega
  have hd1 : d1 = -1 ∨ d1 = 0 ∨ d1 = 1 := mem_orth_diag_fst (d1, d2) hd
  have hd2 : d2 = -1 ∨ d2 = 0 ∨ d2 = 1 := mem_orth_diag_snd (d1, d2) hd
  have hdn : d1 ≠ 0 ∨ d2 ≠ 0 := mem_orth_diag_ne (d1, d2) hd
  have hk7 : k ≤ 7 := by
    rcases hd1 with rfl | rfl | rfl <;> rcases hd2 with rfl | rfl | rfl
    · omega
    · omega
    · omega
    · omega
    · rcases hdn with h | h <;> exact absurd rfl h
    · omega
    · omega
    · omega
    · omega
  have hok : ∀ m, m < k → onb (fl (g.K x) + d1 + (m : Int) * d1) (rk (g.K x) + d2 + (m : Int) * d2) = true ∧
      sqOf (fl (g.K x) + d1 + (m : Int) * d1) (rk (g.K x) + d2 + (m : Int) * d2) ≠ g.K (1 - x) := by
    intro m hm
    have hcast : (↑(m + 1) : Int) = ↑m + 1 := by omega
    have ee1 : fl (g.K x) + d1 + (↑m : Int) * d1 = fl (g.K x) + (↑(m + 1) : Int) * d1 := by
      rw [hcast, Int.add_mul, Int.one_mul]; omega
    have ee2 : rk (g.K x) + d2 + (↑m : Int) * d2 = rk (g.K x) + (↑(m + 1) : Int) * d2 := by
      rw [hcast, Int.add_mul, Int.one_mul]; omega
    have honb : onb (fl (g.K x) + d1 + (↑m : Int) * d1) (rk (g.K x) + d2 + (↑m : Int) * d2) = true := by
      simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
      rw [ee1, ee2]
      rcases hd1 with rfl | rfl | rfl <;> rcases hd2 with rfl | rfl | rfl <;> omega
    refine ⟨honb, ?_⟩
    intro heq
    have h2 := onb_sqOf _ _ honb
    have hfm : fl (g.K (1 - x)) - fl (g.K x) = (↑(m + 1) : Int) * d1 := by
      have e := congrArg fl heq
      rw [h2.2.1] at e
      rw [hcast, Int.add_mul, Int.one_mul]
      omega
    have hrm : rk (g.K (1 - x)) - rk (g.K x) = (↑(m + 1) : Int) * d2 := by
      have e := congrArg rk heq
      rw [h2.2.2] at e
      rw [hcast, Int.add_mul, Int.one_mul]
      omega
    by_cases hmk : m + 1 = k
    · rw [hmk] at hfm hrm
      have hval : g.K (1 - x) = s.val := toSq_inj (g.K (1 - x)) s.val hKo s.isLt
        (by rw [fx_toSq _ hKo, fx_toSq _ s.isLt]; omega)
        (by rw [ry_toSq _ hKo, ry_toSq _ s.isLt]; omega)
      exact hns (congrArg toSq hval).symm
    · have hlt : m + 1 < k := by omega
      have ht := ray_inSeg_intro (g.K x) s.val (g.K (1 - x)) hK s.isLt hKo d1 d2 hd1 hd2 hdn k (m + 1)
        (by omega) hlt hfk' hrk' hfm hrm halt
      rw [ht] at hins
      simp at hins
  obtain ⟨hlen, hget⟩ := go_len_of_ok (d1, d2) (g.K (1 - x)) 8 (fl (g.K x) + (d1, d2).1)
    (rk (g.K x) + (d1, d2).2) k hok (k - 1) (by omega)
  rw [← ray_eq_go] at hlen hget
  have hlast : (g.ray x (d1, d2)).getD (k - 1) 0 = s.val := by
    rw [hget, ← fl_rk_sqOf s.val]
    congr 1
    · show fl (g.K x) + d1 + ↑(k - 1) * d1 = fl s.val
      rw [show (↑(k - 1) : Int) = ↑k - 1 from by omega, Int.sub_mul, Int.one_mul]
      omega
    · show rk (g.K x) + d2 + ↑(k - 1) * d2 = rk s.val
      rw [show (↑(k - 1) : Int) = ↑k - 1 from by omega, Int.sub_mul, Int.one_mul]
      omega
  have hmem : s.val ∈ g.ray x (d1, d2) :=
    List.mem_iff_getElem.mpr ⟨k - 1, hlen, by rw [List.getElem_eq_getD]; exact hlast⟩
  rw [raySquares_eq]
  exact List.mem_flatMap.mpr ⟨(d1, d2), hd, hmem⟩

theorem mem_raySquares_iff (g : Cfg) (hw : g.kw < 64) (hb : g.kb < 64) (hkk : 2 ≤ kdist (toSq g.kw) (toSq g.kb))
    (x : Nat) (hx : x < 2) (s : Sq) :
    s.val ∈ g.raySquares x ↔ aligned (toSq (g.K x)) s = true ∧ s ≠ toSq (g.K (1 - x)) ∧
      inSeg (toSq (g.K x)) s (toSq (g.K (1 - x))) = false := by
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hK : g.K x < 64 := by rcases hx01 with rfl | rfl; exact hw; exact hb
  have hKo : g.K (1 - x) < 64 := by rcases hx01 with rfl | rfl; exact hb; exact hw
  constructor
  · intro hmem
    rw [raySquares_eq] at hmem
    obtain ⟨d, hd, hsd⟩ := List.mem_flatMap.mp hmem
    have hd1 := mem_orth_diag_fst d hd
    have hd2 := mem_orth_diag_snd d hd
    have hdn := mem_orth_diag_ne d hd
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hsd
    obtain ⟨h64, hf0, hr0⟩ := ray_getD g x d hd hK j hj
    have e0 : (g.ray x d).getD j 0 = s.val := (List.getElem_eq_getD 0).symm.trans hjv
    rw [e0] at h64 hf0 hr0
    have hfk : fl s.val - fl (g.K x) = (↑j + 1) * d.1 := by omega
    have hrk : rk s.val - rk (g.K x) = (↑j + 1) * d.2 := by omega
    have halt : aligned (toSq (g.K x)) s = true := by
      simp only [aligned, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, Bool.or_eq_true]
      refine ⟨?_, ?_⟩
      · intro heq
        have e1 := congrArg fx heq
        rw [fx_toSq _ hK, fx_sq] at e1
        have e2 := congrArg ry heq
        rw [ry_toSq _ hK, ry_sq] at e2
        have z1 : (↑j + 1 : Int) * d.1 = 0 := by omega
        have z2 : (↑j + 1 : Int) * d.2 = 0 := by omega
        rcases Int.mul_eq_zero.mp z1 with hz | hdz1; · omega
        rcases Int.mul_eq_zero.mp z2 with hz | hdz2; · omega
        rcases hdn with h | h
        · exact absurd hdz1 h
        · exact absurd hdz2 h
      · by_cases h01 : d.1 = 0
        · left
          rw [h01] at hf0
          rw [fx_toSq _ hK, fx_sq]
          omega
        · by_cases h02 : d.2 = 0
          · left; right
            rw [h02] at hr0
            rw [ry_toSq _ hK, ry_sq]
            omega
          · right
            have e1 : fx (toSq (g.K x)) - fx s = -((↑j + 1) * d.1) := by
              rw [fx_toSq _ hK, fx_sq]; omega
            have e2 : ry (toSq (g.K x)) - ry s = -((↑j + 1) * d.2) := by
              rw [ry_toSq _ hK, ry_sq]; omega
            rw [e1, e2]
            simp only [Int.natAbs_neg, Int.natAbs_mul,
              show (↑j + 1 : Int).natAbs = j + 1 from by
                rw [show (↑j + 1 : Int) = ↑(j + 1) from by omega, Int.natAbs_natCast]]
            have ha1 : d.1.natAbs = 1 := by
              rcases hd1 with h | h | h
              · rw [h]; decide
              · exact absurd h h01
              · rw [h]; decide
            have ha2 : d.2.natAbs = 1 := by
              rcases hd2 with h | h | h
              · rw [h]; decide
              · exact absurd h h02
              · rw [h]; decide
            rw [ha1, ha2]
    have hns : s ≠ toSq (g.K (1 - x)) := by
      intro heq
      have e := congrArg (fun z => z.val) heq
      rw [show (toSq (g.K (1 - x))).val = g.K (1 - x) % 64 from rfl, Nat.mod_eq_of_lt hKo] at e
      have hno : s.val ≠ g.K (1 - x) := by
        rw [ray_eq_go] at hsd
        exact go_ne_o d (g.K (1 - x)) 8 _ _ s.val hsd
      exact hno e
    have hins : inSeg (toSq (g.K x)) s (toSq (g.K (1 - x))) = false := by
      cases hcase : inSeg (toSq (g.K x)) s (toSq (g.K (1 - x)))
      · rfl
      · exfalso
        rw [← toSq_val s] at hcase
        obtain ⟨m, hm1, hmj, hfm, hrm⟩ :=
          ray_inSeg_elim (g.K x) s.val (g.K (1 - x)) hK h64 hKo d.1 d.2 hd1 hd2 hdn j hfk hrk hcase
        have hcast : (↑(m - 1) + 1 : Int) = ↑m := by omega
        have hml : m - 1 < (g.ray x d).length := by omega
        obtain ⟨h64m, hfmj, hrmj⟩ := ray_getD g x d hd hK (m - 1) hml
        rw [hcast] at hfmj hrmj
        have hfeq : fl (g.K (1 - x)) = fl ((g.ray x d).getD (m - 1) 0) := by omega
        have hreq : rk (g.K (1 - x)) = rk ((g.ray x d).getD (m - 1) 0) := by omega
        have hvaleq : (g.ray x d).getD (m - 1) 0 = g.K (1 - x) := by
          rw [← fl_rk_sqOf ((g.ray x d).getD (m - 1) 0), ← fl_rk_sqOf (g.K (1 - x)), hfeq, hreq]
        have hmem3 : (g.ray x d).getD (m - 1) 0 ∈ g.ray x d :=
          List.mem_iff_getElem.mpr ⟨m - 1, hml, by rw [List.getElem_eq_getD]⟩
        rw [ray_eq_go] at hmem3
        have hno3 := go_ne_o d (g.K (1 - x)) 8 _ _ _ hmem3
        have hconv := congrArg (fun l : List Nat => l.getD (m - 1) 0) (ray_eq_go g x d)
        rw [hconv] at hvaleq
        rw [hvaleq] at hno3
        exact absurd rfl hno3
    exact ⟨halt, hns, hins⟩
  · rintro ⟨halt, hns, hins⟩
    have halt0 := halt
    simp only [aligned, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, Bool.or_eq_true] at halt
    obtain ⟨hne00, hdir⟩ := halt
    rcases hdir with (hfx | hry) | habs
    · have hfx' : fl (g.K x) = fl s.val := by rw [fx_toSq _ hK, fx_sq] at hfx; exact hfx
      have hrne : rk s.val ≠ rk (g.K x) := by
        intro h
        apply hne00
        have h1 : g.K x = s.val := toSq_inj (g.K x) s.val hK s.isLt
          (by rw [fx_toSq _ hK, fx_toSq _ s.isLt]; exact hfx')
          (by rw [ry_toSq _ hK, ry_toSq _ s.isLt]; exact h.symm)
        have h2 : toSq (g.K x) = toSq s.val := congrArg toSq h1
        rwa [toSq_val s] at h2
      have hrne0 : rk s.val - rk (g.K x) ≠ 0 := by omega
      by_cases hsgn : 0 ≤ rk s.val - rk (g.K x)
      · have hkΔ : (↑(rk s.val - rk (g.K x)).natAbs : Int) = rk s.val - rk (g.K x) :=
          Int.natAbs_of_nonneg hsgn
        exact mem_ray_of_dir g x hK hKo s 0 1 (by decide) ((rk s.val - rk (g.K x)).natAbs) (by omega)
          (by omega) (by rw [Int.mul_one]; omega) hns hins halt0
      · have hsgn' : rk s.val - rk (g.K x) < 0 := by omega
        have hkΔ : (↑(rk s.val - rk (g.K x)).natAbs : Int) = -(rk s.val - rk (g.K x)) := by omega
        exact mem_ray_of_dir g x hK hKo s 0 (-1) (by decide) ((rk s.val - rk (g.K x)).natAbs) (by omega)
          (by omega) (by rw [Int.mul_neg, Int.mul_one]; omega) hns hins halt0
    · have hry' : rk (g.K x) = rk s.val := by rw [ry_toSq _ hK, ry_sq] at hry; exact hry
      have hfne : fl s.val ≠ fl (g.K x) := by
        intro h
        apply hne00
        have h1 : g.K x = s.val := toSq_inj (g.K x) s.val hK s.isLt
          (by rw [fx_toSq _ hK, fx_toSq _ s.isLt]; exact h.symm)
          (by rw [ry_toSq _ hK, ry_toSq _ s.isLt]; exact hry')
        have h2 : toSq (g.K x) = toSq s.val := congrArg toSq h1
        rwa [toSq_val s] at h2
      have hfne0 : fl s.val - fl (g.K x) ≠ 0 := by omega
      by_cases hsgn : 0 ≤ fl s.val - fl (g.K x)
      · have hkΔ : (↑(fl s.val - fl (g.K x)).natAbs : Int) = fl s.val - fl (g.K x) :=
          Int.natAbs_of_nonneg hsgn
        exact mem_ray_of_dir g x hK hKo s 1 0 (by decide) ((fl s.val - fl (g.K x)).natAbs) (by omega)
          (by rw [Int.mul_one]; omega) (by omega) hns hins halt0
      · have hsgn' : fl s.val - fl (g.K x) < 0 := by omega
        have hkΔ : (↑(fl s.val - fl (g.K x)).natAbs : Int) = -(fl s.val - fl (g.K x)) := by omega
        exact mem_ray_of_dir g x hK hKo s (-1) 0 (by decide) ((fl s.val - fl (g.K x)).natAbs) (by omega)
          (by rw [Int.mul_neg, Int.mul_one]; omega) (by omega) hns hins halt0
    · rw [fx_toSq _ hK, fx_sq, ry_toSq _ hK, ry_sq] at habs
      have hfl0 : fl (g.K x) - fl s.val = -(fl s.val - fl (g.K x)) := by omega
      have hrk0 : rk (g.K x) - rk s.val = -(rk s.val - rk (g.K x)) := by omega
      rw [hfl0, hrk0, Int.natAbs_neg, Int.natAbs_neg] at habs
      have hne2 : fl s.val - fl (g.K x) ≠ 0 ∧ rk s.val - rk (g.K x) ≠ 0 := by
        constructor
        · intro h0
          have h0' : (fl s.val - fl (g.K x)).natAbs = 0 := by rw [h0]; rfl
          have h0r : (rk s.val - rk (g.K x)).natAbs = 0 := by rw [← habs]; exact h0'
          have hrk0eq : rk s.val - rk (g.K x) = 0 := Int.natAbs_eq_zero.mp h0r
          have h1 : g.K x = s.val := toSq_inj (g.K x) s.val hK s.isLt
            (by rw [fx_toSq _ hK, fx_toSq _ s.isLt]; omega)
            (by rw [ry_toSq _ hK, ry_toSq _ s.isLt]; omega)
          exact hne00 (congrArg toSq h1 |>.trans (toSq_val s))
        · intro h0
          have h0' : (rk s.val - rk (g.K x)).natAbs = 0 := by rw [h0]; rfl
          have hfl0eq : fl s.val - fl (g.K x) = 0 := Int.natAbs_eq_zero.mp (by rw [habs]; exact h0')
          have h1 : g.K x = s.val := toSq_inj (g.K x) s.val hK s.isLt
            (by rw [fx_toSq _ hK, fx_toSq _ s.isLt]; omega)
            (by rw [ry_toSq _ hK, ry_toSq _ s.isLt]; omega)
          exact hne00 (congrArg toSq h1 |>.trans (toSq_val s))
      obtain ⟨hfne0, hrne0⟩ := hne2
      by_cases hs1 : 0 ≤ fl s.val - fl (g.K x)
      · by_cases hs2 : 0 ≤ rk s.val - rk (g.K x)
        · exact mem_ray_of_dir g x hK hKo s 1 1 (by decide) ((fl s.val - fl (g.K x)).natAbs) (by omega)
            (by rw [Int.mul_one]; omega) (by rw [Int.mul_one]; omega) hns hins halt0
        · exact mem_ray_of_dir g x hK hKo s 1 (-1) (by decide) ((fl s.val - fl (g.K x)).natAbs) (by omega)
            (by rw [Int.mul_one]; omega) (by rw [Int.mul_neg, Int.mul_one]; omega) hns hins halt0
      · by_cases hs2 : 0 ≤ rk s.val - rk (g.K x)
        · exact mem_ray_of_dir g x hK hKo s (-1) 1 (by decide) ((fl s.val - fl (g.K x)).natAbs) (by omega)
            (by rw [Int.mul_neg, Int.mul_one]; omega) (by rw [Int.mul_one]; omega) hns hins halt0
        · exact mem_ray_of_dir g x hK hKo s (-1) (-1) (by decide) ((fl s.val - fl (g.K x)).natAbs) (by omega)
            (by rw [Int.mul_neg, Int.mul_one]; omega) (by rw [Int.mul_neg, Int.mul_one]; omega) hns hins halt0

theorem raySquares_lt (g : Cfg) (hw : g.kw < 64) (hb : g.kb < 64) (x : Nat) (hx : x < 2) (s : Nat)
    (h : s ∈ g.raySquares x) : s < 64 := by
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hK : g.K x < 64 := by rcases hx01 with rfl | rfl; exact hw; exact hb
  rw [raySquares_eq] at h
  obtain ⟨d, hd, hsd⟩ := List.mem_flatMap.mp h
  obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hsd
  have h64 := (ray_getD g x d hd hK j hj).1
  have e : (g.ray x d).getD j 0 = s := (List.getElem_eq_getD 0).symm.trans hjv
  rwa [e] at h64

theorem insertAlt_keys (al : List (Nat × List (List ALit))) (s : Nat) (c : List ALit) :
    ((insertAlt al s c).map (·.1)) = if al.any (·.1 == s) then al.map (·.1) else al.map (·.1) ++ [s] := by
  unfold insertAlt
  split
  · rw [List.map_map]
    apply List.map_congr_left
    intro e he
    simp only [Function.comp]
    split <;> rfl
  · rw [List.map_append]; rfl

theorem insertAlt_nodup (al : List (Nat × List (List ALit))) (s : Nat) (c : List ALit)
    (h : (al.map (·.1)).Nodup) : ((insertAlt al s c).map (·.1)).Nodup := by
  by_cases hany : al.any (·.1 == s) = true
  · rw [insertAlt_keys, if_pos hany]
    exact h
  · rw [insertAlt_keys, if_neg hany]
    have hns : s ∉ al.map (·.1) := by
      intro hm
      obtain ⟨e, he, hfst⟩ := List.mem_map.mp hm
      exact hany (List.any_eq_true.mpr ⟨e, he, beq_iff_eq.mpr hfst⟩)
    rw [List.nodup_append]
    refine ⟨h, by simp, fun a ha b hb => ?_⟩
    intro hab
    have hb' : b = s := List.mem_singleton.mp hb
    exact hns (hab.trans hb' ▸ ha)

theorem nodup_foldl {α : Type} (step : List (Nat × List (List ALit)) → α → List (Nat × List (List ALit)))
    (hstep : ∀ al a, (al.map (·.1)).Nodup → ((step al a).map (·.1)).Nodup) :
    ∀ (L : List α) (init : List (Nat × List (List ALit))), (init.map (·.1)).Nodup →
      ((L.foldl step init).map (·.1)).Nodup := by
  intro L
  induction L with
  | nil => intro init h; exact h
  | cons a as ih =>
    intro init h
    rw [List.foldl_cons]
    exact ih _ (hstep _ _ h)

theorem insertAlt_keys_nodup_step (g : Cfg) (x : Nat) :
    ∀ al s, (al.map (·.1)).Nodup →
      (((fun al1 => if attacksGeom P (1 - x) s (g.K x) then insertAlt al1 s [.x s (5 * (1 - x) + P)] else al1)
        (if attacksGeom N (1 - x) s (g.K x) then insertAlt al s [.x s (5 * (1 - x) + N)] else al)).map (·.1)).Nodup := by
  intro al s h
  dsimp only
  split
  · split
    · exact insertAlt_nodup _ _ _ (insertAlt_nodup _ _ _ h)
    · exact insertAlt_nodup _ _ _ h
  · split
    · exact insertAlt_nodup _ _ _ h
    · exact h

theorem mem_insertAlt (al : List (Nat × List (List ALit))) (hal : (al.map (·.1)).Nodup) (s : Nat) (c : List ALit)
    (s' : Nat) (cs : List (List ALit)) :
    (s', cs) ∈ insertAlt al s c ↔
      ((s', cs) ∈ al ∧ s' ≠ s) ∨
        (s' = s ∧ ((∃ cs0, (s, cs0) ∈ al ∧ cs = cs0 ++ [c]) ∨ ((∀ cs0, (s, cs0) ∉ al) ∧ cs = [c]))) := by
  unfold insertAlt
  by_cases hs : al.any (·.1 == s) = true
  · rw [if_pos hs]
    constructor
    · intro hm
      obtain ⟨⟨a, b⟩, he, hfe⟩ := List.mem_map.mp hm
      by_cases hes : (a == s) = true
      · rw [if_pos hes] at hfe
        have h12 := Prod.ext_iff.mp hfe
        have hae : a = s := beq_iff_eq.mp hes
        rw [hae] at he
        exact Or.inr ⟨h12.1.symm.trans hae, Or.inl ⟨b, he, h12.2.symm⟩⟩
      · rw [if_neg hes] at hfe
        have h12 := Prod.ext_iff.mp hfe
        have hmem : (s', cs) ∈ al := hfe ▸ he
        refine Or.inl ⟨hmem, fun hs's => ?_⟩
        exact hes (beq_iff_eq.mpr (h12.1.trans hs's))
    · intro hr
      rcases hr with ⟨hm, hne⟩ | ⟨hseq, hsub⟩
      · apply List.mem_map.mpr
        exact ⟨(s', cs), hm, if_neg (fun hb => hne (beq_iff_eq.mp hb))⟩
      · rw [hseq] at *
        rcases hsub with ⟨cs0, hm0, hmk⟩ | ⟨hnone, hmk⟩
        · apply List.mem_map.mpr
          refine ⟨(s, cs0), hm0, ?_⟩
          rw [if_pos (show ((s, cs0).1 == s) = true from beq_iff_eq.mpr rfl)]
          exact Prod.ext rfl hmk.symm
        · obtain ⟨⟨a, b⟩, he, hbe⟩ := List.any_eq_true.mp hs
          have hae : a = s := beq_iff_eq.mp hbe
          rw [hae] at he
          exact absurd he (hnone b)
  · rw [if_neg hs]
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · refine Or.inl ⟨hm, fun hs's => ?_⟩
        exact hs (List.any_eq_true.mpr ⟨(s', cs), hm, show ((s', cs).1 == s) = true from beq_iff_eq.mpr hs's⟩)
      · have h12 := Prod.ext_iff.mp (List.mem_singleton.mp hm)
        exact Or.inr ⟨h12.1, Or.inr ⟨fun cs0 hmc =>
          hs (List.any_eq_true.mpr ⟨(s, cs0), hmc, show ((s, cs0).1 == s) = true from beq_iff_eq.mpr rfl⟩), h12.2⟩⟩
    · intro hr
      rcases hr with ⟨hm, hne⟩ | ⟨hseq, hsub⟩
      · exact List.mem_append_left _ hm
      · rw [hseq] at *
        rcases hsub with ⟨cs0, hm0, hmk⟩ | ⟨hnone, hmk⟩
        · exact absurd (List.any_eq_true.mpr ⟨(s, cs0), hm0, show ((s, cs0).1 == s) = true from beq_iff_eq.mpr rfl⟩) hs
        · subst hmk
          exact List.mem_append_right _ (List.mem_singleton_self _)

def baseStep (g : Cfg) (x : Nat) (al : List (Nat × List (List ALit))) (s : Nat) : List (Nat × List (List ALit)) :=
  (fun al1 => if attacksGeom P (1 - x) s (g.K x) then insertAlt al1 s [.x s (5 * (1 - x) + P)] else al1)
    (if attacksGeom N (1 - x) s (g.K x) then insertAlt al s [.x s (5 * (1 - x) + N)] else al)

def pieceStep (g : Cfg) (x : Nat) (d : Int × Int) (j : Nat) (al : List (Nat × List (List ALit))) :
    List (Nat × List (List ALit)) :=
  [Q, if orth.contains d then R else B].foldl (fun al p =>
    insertAlt al ((g.ray x d).getD j 0)
      ((clearLit (g.ray x d) j).toList ++ [.x ((g.ray x d).getD j 0) (5 * (1 - x) + p)])) al

def dirStep (g : Cfg) (x : Nat) (al : List (Nat × List (List ALit))) (d : Int × Int) :
    List (Nat × List (List ALit)) :=
  (List.range (g.ray x d).length).foldl (fun al j => pieceStep g x d j al) al

def attAltsOf (g : Cfg) (x : Nat) : List (Nat × List (List ALit)) :=
  (orth ++ diag).foldl (fun al d => dirStep g x al d) (g.NK.foldl (fun al s => baseStep g x al s) [])

theorem attAlts_eq (g : Cfg) (x : Nat) : attAlts g x = attAltsOf g x := rfl

theorem baseStep_nodup (g : Cfg) (x : Nat) (al : List (Nat × List (List ALit)))
    (h : (al.map (·.1)).Nodup) (s0 : Nat) : ((baseStep g x al s0).map (·.1)).Nodup := by
  simp only [baseStep]
  split
  · split
    · exact insertAlt_nodup _ _ _ (insertAlt_nodup _ _ _ h)
    · exact insertAlt_nodup _ _ _ h
  · split
    · exact insertAlt_nodup _ _ _ h
    · exact h

theorem pieceStep_nodup (g : Cfg) (x : Nat) (d : Int × Int) (j : Nat) (al : List (Nat × List (List ALit)))
    (h : (al.map (·.1)).Nodup) : ((pieceStep g x d j al).map (·.1)).Nodup := by
  simp only [pieceStep, List.foldl_cons, List.foldl_nil]
  exact insertAlt_nodup _ _ _ (insertAlt_nodup _ _ _ h)

theorem dirStep_nodup (g : Cfg) (x : Nat) (al : List (Nat × List (List ALit)))
    (h : (al.map (·.1)).Nodup) (d : Int × Int) : ((dirStep g x al d).map (·.1)).Nodup := by
  simp only [dirStep]
  exact nodup_foldl _ (fun al2 j h2 => pieceStep_nodup g x d j al2 h2) _ _ h

theorem attAlts_keys_nodup (g : Cfg) (x : Nat) : ((attAlts g x).map (·.1)).Nodup := by
  rw [attAlts_eq, attAltsOf]
  exact nodup_foldl _ (fun al d h => dirStep_nodup g x al h d) _ _
    (nodup_foldl _ (fun al s h => baseStep_nodup g x al h s) _ _ List.nodup_nil)

def pieceList (g : Cfg) (x : Nat) (d : Int × Int) (j : Nat) : List (Nat × List ALit) :=
  [((g.ray x d).getD j 0, (clearLit (g.ray x d) j).toList ++ [.x ((g.ray x d).getD j 0) (5 * (1 - x) + Q)]),
    ((g.ray x d).getD j 0, (clearLit (g.ray x d) j).toList ++
      [.x ((g.ray x d).getD j 0) (5 * (1 - x) + (if orth.contains d then R else B))])]

def dirList (g : Cfg) (x : Nat) (d : Int × Int) : List (Nat × List ALit) :=
  (List.range (g.ray x d).length).flatMap (pieceList g x d)

def npList (g : Cfg) (x : Nat) (s : Nat) : List (Nat × List ALit) :=
  (if attacksGeom N (1 - x) s (g.K x) then [(s, [.x s (5 * (1 - x) + N)])] else []) ++
    (if attacksGeom P (1 - x) s (g.K x) then [(s, [.x s (5 * (1 - x) + P)])] else [])

def insertKeys (ks : List (Nat × List ALit)) (acc : List (Nat × List (List ALit))) :
    List (Nat × List (List ALit)) :=
  ks.foldl (fun al p => insertAlt al p.1 p.2) acc

theorem insertKeys_app (l1 l2 : List (Nat × List ALit)) (acc : List (Nat × List (List ALit))) :
    insertKeys (l1 ++ l2) acc = insertKeys l2 (insertKeys l1 acc) := by
  simp only [insertKeys, List.foldl_append]

theorem baseStep_eq (g : Cfg) (x : Nat) (acc : List (Nat × List (List ALit))) (s0 : Nat) :
    baseStep g x acc s0 = insertKeys (npList g x s0) acc := by
  simp only [baseStep, npList, insertKeys]
  rw [List.foldl_append]
  split
  · split
    · rw [List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
    · rw [List.foldl_cons, List.foldl_nil, List.foldl_nil]
  · split
    · rw [List.foldl_nil, List.foldl_cons, List.foldl_nil]
    · rw [List.foldl_nil, List.foldl_nil]

theorem np_list_foldl (g : Cfg) (x : Nat) :
    ∀ (L : List Nat) (acc : List (Nat × List (List ALit))),
      L.foldl (fun al s => baseStep g x al s) acc = insertKeys (L.flatMap (npList g x)) acc := by
  intro L
  induction L with
  | nil => intro acc; rw [List.foldl_nil]; rfl
  | cons s0 ss ih =>
    intro acc
    rw [List.foldl_cons, baseStep_eq, List.flatMap_cons, insertKeys_app]
    exact ih _

theorem pieceStep_eq (g : Cfg) (x : Nat) (d : Int × Int) (j : Nat) (acc : List (Nat × List (List ALit))) :
    pieceStep g x d j acc = insertKeys (pieceList g x d j) acc := by
  simp only [pieceStep, pieceList, insertKeys, List.foldl_cons, List.foldl_nil]

theorem piece_list_foldl (g : Cfg) (x : Nat) (d : Int × Int) :
    ∀ (L : List Nat) (acc : List (Nat × List (List ALit))),
      L.foldl (fun al j => pieceStep g x d j al) acc = insertKeys (L.flatMap (pieceList g x d)) acc := by
  intro L
  induction L with
  | nil => intro acc; rw [List.foldl_nil]; rfl
  | cons j js ih =>
    intro acc
    rw [List.foldl_cons, pieceStep_eq, List.flatMap_cons, insertKeys_app]
    exact ih _

theorem dirStep_eq (g : Cfg) (x : Nat) (acc : List (Nat × List (List ALit))) (d : Int × Int) :
    dirStep g x acc d = insertKeys (dirList g x d) acc := by
  simp only [dirStep, dirList]
  exact piece_list_foldl g x d _ _

theorem dir_list_foldl (g : Cfg) (x : Nat) :
    ∀ (L : List (Int × Int)) (acc : List (Nat × List (List ALit))),
      L.foldl (fun al d => dirStep g x al d) acc = insertKeys (L.flatMap (dirList g x)) acc := by
  intro L
  induction L with
  | nil => intro acc; rw [List.foldl_nil]; rfl
  | cons d ds ih =>
    intro acc
    rw [List.foldl_cons, dirStep_eq, List.flatMap_cons, insertKeys_app]
    exact ih _

theorem attAlts_eq_keys (g : Cfg) (x : Nat) :
    attAlts g x =
      insertKeys (g.NK.flatMap (npList g x) ++ (orth ++ diag).flatMap (dirList g x)) [] := by
  rw [attAlts_eq, attAltsOf, dir_list_foldl, np_list_foldl, ← insertKeys_app]

def MemAt (al : List (Nat × List (List ALit))) (s : Nat) (conj : List ALit) : Prop :=
  ∃ cs, (s, cs) ∈ al ∧ conj ∈ cs

theorem memAt_insertAlt (al : List (Nat × List (List ALit))) (hal : (al.map (·.1)).Nodup)
    (s0 : Nat) (c : List ALit) (s : Nat) (conj : List ALit) :
    MemAt (insertAlt al s0 c) s conj ↔ MemAt al s conj ∨ (s = s0 ∧ conj = c) := by
  constructor
  · rintro ⟨cs, hm, hcm⟩
    rw [mem_insertAlt al hal s0 c s cs] at hm
    rcases hm with ⟨hmal, hns⟩ | ⟨hseq, hsub⟩
    · exact Or.inl ⟨cs, hmal, hcm⟩
    · rcases hsub with ⟨cs0, hm0, hmk⟩ | ⟨hnone, hmk⟩
      · rw [hmk] at hcm
        rcases List.mem_append.mp hcm with h | h
        · exact Or.inl ⟨cs0, by rw [hseq]; exact hm0, h⟩
        · exact Or.inr ⟨hseq, List.mem_singleton.mp h⟩
      · rw [hmk] at hcm
        exact Or.inr ⟨hseq, List.mem_singleton.mp hcm⟩
  · rintro (⟨cs, hmal, hcm⟩ | ⟨hseq, hcj⟩)
    · by_cases hss : s = s0
      · rw [hss] at hmal ⊢
        exact ⟨cs ++ [c], (mem_insertAlt al hal s0 c s0 (cs ++ [c])).mpr (Or.inr ⟨rfl, Or.inl ⟨cs, hmal, rfl⟩⟩),
          List.mem_append_left _ hcm⟩
      · exact ⟨cs, (mem_insertAlt al hal s0 c s cs).mpr (Or.inl ⟨hmal, hss⟩), hcm⟩
    · by_cases hex : ∃ cs0, (s0, cs0) ∈ al
      · obtain ⟨cs0, hm0⟩ := hex
        refine ⟨cs0 ++ [c], (mem_insertAlt al hal s0 c s (cs0 ++ [c])).mpr (Or.inr ⟨hseq, Or.inl ⟨cs0, hm0, rfl⟩⟩), ?_⟩
        rw [hcj]; exact List.mem_append_right _ (List.mem_singleton_self c)
      · refine ⟨[c], (mem_insertAlt al hal s0 c s [c]).mpr (Or.inr ⟨hseq, Or.inr ⟨?_, rfl⟩⟩), ?_⟩
        · intro cs0 hm0; exact hex ⟨cs0, hm0⟩
        · rw [hcj]; exact List.mem_singleton_self c


theorem memAtt_insAll (ks : List (Nat × List ALit)) :
    ∀ (al0 : List (Nat × List (List ALit))) (hal : (al0.map (·.1)).Nodup) (s : Nat) (conj : List ALit),
    MemAt (insertKeys ks al0) s conj ↔ MemAt al0 s conj ∨ (s, conj) ∈ ks := by
  induction ks with
  | nil =>
    intro al0 hal s conj
    rw [show insertKeys [] al0 = al0 from rfl]
    constructor
    · intro hm; exact Or.inl hm
    · rintro (hm | hm); exact hm; exact absurd hm (List.not_mem_nil (a := (s, conj)))
  | cons p ks ih =>
    intro al0 hal s conj
    rw [show insertKeys (p :: ks) al0 = insertKeys ks (insertAlt al0 p.1 p.2) from by
      simp only [insertKeys]; rw [List.foldl_cons]]
    rw [ih _ (insertAlt_nodup _ _ _ hal)]
    rw [memAt_insertAlt al0 hal p.1 p.2 s conj]
    constructor
    · rintro ((hm | ⟨h1, h2⟩) | h3)
      · exact Or.inl hm
      · exact Or.inr (List.mem_cons.mpr (Or.inl (Prod.ext_iff.mpr ⟨h1, h2⟩)))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h3))
    · rintro (hm | h1)
      · exact Or.inl (Or.inl hm)
      · rcases List.mem_cons.mp h1 with h1 | h1
        · obtain ⟨hA, hB⟩ := Prod.ext_iff.mp h1
          exact Or.inl (Or.inr ⟨hA, hB⟩)
        · exact Or.inr h1

theorem np_list_mem (g : Cfg) (x s0 : Nat) (s : Nat) (conj : List ALit) :
    (s, conj) ∈ npList g x s0 ↔
      (attacksGeom N (1 - x) s0 (g.K x) = true ∧ s = s0 ∧ conj = [.x s0 (5 * (1 - x) + N)]) ∨
      (attacksGeom P (1 - x) s0 (g.K x) = true ∧ s = s0 ∧ conj = [.x s0 (5 * (1 - x) + P)]) := by
  by_cases hN : attacksGeom N (1 - x) s0 (g.K x) = true <;> by_cases hP : attacksGeom P (1 - x) s0 (g.K x) = true
  · rw [show npList g x s0 = [(s0, [.x s0 (5 * (1 - x) + N)]), (s0, [.x s0 (5 * (1 - x) + P)])] from by
      simp only [npList]; rw [if_pos hN, if_pos hP]; rfl]
    rw [List.mem_cons, List.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨hN, (Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2⟩
      · exact Or.inr ⟨hP, (Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2⟩
    · rintro (⟨_, h1, h2⟩ | ⟨_, h1, h2⟩)
      · exact Or.inl (Prod.ext_iff.mpr ⟨h1, h2⟩)
      · exact Or.inr (Prod.ext_iff.mpr ⟨h1, h2⟩)
  · rw [show npList g x s0 = [(s0, [.x s0 (5 * (1 - x) + N)])] from by
      simp only [npList]; rw [if_pos hN, if_neg hP]; rfl]
    rw [List.mem_singleton]
    constructor
    · intro h
      exact Or.inl ⟨hN, (Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2⟩
    · rintro (⟨_, h1, h2⟩ | ⟨h2, -, -⟩)
      · exact Prod.ext_iff.mpr ⟨h1, h2⟩
      · exact absurd h2 hP
  · rw [show npList g x s0 = [(s0, [.x s0 (5 * (1 - x) + P)])] from by
      simp only [npList]; rw [if_neg hN, if_pos hP]; rfl]
    rw [List.mem_singleton]
    constructor
    · intro h
      exact Or.inr ⟨hP, (Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2⟩
    · rintro (⟨h1, -, -⟩ | ⟨_, h1, h2⟩)
      · exact absurd h1 hN
      · exact Prod.ext_iff.mpr ⟨h1, h2⟩
  · rw [show npList g x s0 = [] from by
      simp only [npList]; rw [if_neg hN, if_neg hP]; rfl]
    rw [show ((s, conj) ∈ ([] : List (Nat × List ALit))) = False from propext ⟨List.not_mem_nil (a := (s, conj)), False.elim⟩]
    constructor
    · exact False.elim
    · rintro (⟨h1, -, -⟩ | ⟨h1, -, -⟩)
      · exact absurd h1 hN
      · exact absurd h1 hP

theorem npPart_mem (g : Cfg) (x : Nat) (s : Nat) (conj : List ALit) :
    (s, conj) ∈ g.NK.flatMap (npList g x) ↔
      (s ∈ g.NK ∧ attacksGeom N (1 - x) s (g.K x) = true ∧ conj = [.x s (5 * (1 - x) + N)]) ∨
      (s ∈ g.NK ∧ attacksGeom P (1 - x) s (g.K x) = true ∧ conj = [.x s (5 * (1 - x) + P)]) := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨s0, hs0, hm⟩
    rw [np_list_mem] at hm
    rcases hm with ⟨hcond, hseq, hceq⟩ | ⟨hcond, hseq, hceq⟩
    · subst hseq; subst hceq
      exact Or.inl ⟨hs0, hcond, rfl⟩
    · subst hseq; subst hceq
      exact Or.inr ⟨hs0, hcond, rfl⟩
  · rintro (⟨hs, hcond, hceq⟩ | ⟨hs, hcond, hceq⟩)
    · exact ⟨s, hs, np_list_mem _ _ _ _ _ |>.mpr (Or.inl ⟨hcond, rfl, hceq⟩)⟩
    · exact ⟨s, hs, np_list_mem _ _ _ _ _ |>.mpr (Or.inr ⟨hcond, rfl, hceq⟩)⟩

theorem dirList_mem (g : Cfg) (x : Nat) (d : Int × Int) (s : Nat) (conj : List ALit) :
    (s, conj) ∈ dirList g x d ↔
      ∃ j, j < (g.ray x d).length ∧ s = (g.ray x d).getD j 0 ∧
        (conj = (clearLit (g.ray x d) j).toList ++ [.x ((g.ray x d).getD j 0) (5 * (1 - x) + Q)] ∨
          conj = (clearLit (g.ray x d) j).toList ++
            [.x ((g.ray x d).getD j 0) (5 * (1 - x) + (if orth.contains d then R else B))]) := by
  rw [dirList, List.mem_flatMap]
  constructor
  · rintro ⟨j, hj, hm⟩
    rw [List.mem_range] at hj
    refine ⟨j, hj, ?_⟩
    rw [pieceList, List.mem_cons, List.mem_singleton] at hm
    rcases hm with h | h
    · exact ⟨(Prod.ext_iff.mp h).1, Or.inl (Prod.ext_iff.mp h).2⟩
    · exact ⟨(Prod.ext_iff.mp h).1, Or.inr (Prod.ext_iff.mp h).2⟩
  · rintro ⟨j, hj, hseq, hconj⟩
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    rw [pieceList, List.mem_cons, List.mem_singleton]
    rcases hconj with h | h
    · exact Or.inl (Prod.ext_iff.mpr ⟨hseq, h⟩)
    · exact Or.inr (Prod.ext_iff.mpr ⟨hseq, h⟩)

theorem dirPart_mem (g : Cfg) (x : Nat) (s : Nat) (conj : List ALit) :
    (s, conj) ∈ (orth ++ diag).flatMap (dirList g x) ↔
      ∃ d, d ∈ orth ++ diag ∧ ∃ j, j < (g.ray x d).length ∧ s = (g.ray x d).getD j 0 ∧
        (conj = (clearLit (g.ray x d) j).toList ++ [.x ((g.ray x d).getD j 0) (5 * (1 - x) + Q)] ∨
          conj = (clearLit (g.ray x d) j).toList ++
            [.x ((g.ray x d).getD j 0) (5 * (1 - x) + (if orth.contains d then R else B))]) := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨d, hd, hm⟩
    exact ⟨d, hd, (dirList_mem g x d s conj).mp hm⟩
  · rintro ⟨d, hd, hm⟩
    exact ⟨d, hd, (dirList_mem g x d s conj).mpr hm⟩

theorem mem_attAlts_iff (g : Cfg) (x : Nat) (hx : x < 2) (s : Nat) (conj : List ALit) :
    (∃ cs, (s, cs) ∈ attAlts g x ∧ conj ∈ cs) ↔
      (s ∈ g.NK ∧ attacksGeom N (1 - x) s (g.K x) = true ∧ conj = [.x s (5 * (1 - x) + N)]) ∨
      (s ∈ g.NK ∧ attacksGeom P (1 - x) s (g.K x) = true ∧ conj = [.x s (5 * (1 - x) + P)]) ∨
      (∃ d ∈ orth ++ diag, ∃ j, j < (g.ray x d).length ∧ s = (g.ray x d).getD j 0 ∧
        ∃ pc ∈ [Q, if orth.contains d then R else B],
          conj = (clearLit (g.ray x d) j).toList ++ [.x s (5 * (1 - x) + pc)]) := by
  show MemAt (attAlts g x) s conj ↔ _
  rw [attAlts_eq_keys]
  rw [memAtt_insAll _ [] List.nodup_nil s conj]
  rw [show MemAt [] s conj = False from propext ⟨fun ⟨cs, hm, _⟩ => absurd hm (List.not_mem_nil (a := (s, cs))), False.elim⟩]
  rw [false_or]
  rw [List.mem_append, npPart_mem, dirPart_mem]
  constructor
  · rintro ((hN | hP) | hD)
    · exact Or.inl hN
    · exact Or.inr (Or.inl hP)
    · obtain ⟨d, hd, j, hj, hseq, hconj⟩ := hD
      refine Or.inr (Or.inr ⟨d, hd, j, hj, hseq, ?_⟩)
      rcases hconj with h | h
      · refine ⟨Q, List.mem_cons_self, ?_⟩
        rw [hseq]; exact h
      · refine ⟨if orth.contains d then R else B, List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)), ?_⟩
        rw [hseq]; exact h
  · rintro (hN | hP | hD)
    · exact Or.inl (Or.inl hN)
    · exact Or.inl (Or.inr hP)
    · obtain ⟨d, hd, j, hj, hseq, pc, hpc, hceq⟩ := hD
      rw [List.mem_cons, List.mem_singleton] at hpc
      refine Or.inr ⟨d, hd, j, hj, hseq, ?_⟩
      rcases hpc with rfl | rfl
      · rw [hseq] at hceq
        exact Or.inl hceq
      · rw [hseq] at hceq
        exact Or.inr hceq

end Bridge

section Alloc

def Ext {α : Type} (x : AM α) : Prop :=
  ∀ a : Alloc, a.roles.size = a.nv →
    (x.run a).2.roles.size = (x.run a).2.nv ∧ a.roles.toList <+: (x.run a).2.roles.toList

theorem fresh_run (r : Role) (a : Alloc) :
    (fresh r).run a = (((a.nv + 1 : Nat) : Int), { nv := a.nv + 1, roles := a.roles.push r }) := rfl

theorem fresh_ext (r : Role) : Ext (fresh r) := by
  intro a ha
  simp only [fresh_run, Array.size_push, ha, Array.toList_push, true_and]
  exact List.prefix_append _ _

theorem pure_ext {α : Type} (v : α) : Ext (pure v : AM α) := by
  intro a ha
  exact ⟨ha, List.prefix_refl _⟩

theorem run_bind {α β : Type} (x : AM α) (f : α → AM β) (a : Alloc) :
    (x >>= f).run a = (f (x.run a).1).run (x.run a).2 := rfl

theorem run_pure {α : Type} (v : α) (a : Alloc) : (pure v : AM α).run a = (v, a) := rfl

theorem bind_ext {α β : Type} (x : AM α) (f : α → AM β) (hx : Ext x) (hf : ∀ v, Ext (f v)) : Ext (x >>= f) := by
  intro a ha
  obtain ⟨hs1, hp1⟩ := hx a ha
  obtain ⟨hs2, hp2⟩ := hf (x.run a).1 (x.run a).2 hs1
  exact ⟨hs2, hp1.trans hp2⟩

theorem mapM_ext {α β : Type} (l : List α) (f : α → AM β) (h : ∀ v ∈ l, Ext (f v)) : Ext (l.mapM f) := by
  induction l with
  | nil => rw [List.mapM_nil]; exact pure_ext []
  | cons a as ih =>
    rw [List.mapM_cons]
    apply bind_ext
    · exact h a (List.mem_cons_self)
    · intro v
      apply bind_ext
      · exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      · intro vs
        exact pure_ext _

theorem map_range_succ (base n : Nat) :
    ((List.range (n + 1)).map fun i => ((base + i + 1 : Nat) : Int)) =
      ((base + 1 : Nat) : Int) :: (List.range n).map fun i => ((base + 1 + i + 1 : Nat) : Int) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.cons.injEq]
  refine ⟨rfl, ?_⟩
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hlt : i < n
  · rw [List.getElem?_range hlt]
    show some (((fun j => ((base + j + 1 : Nat) : Int)) (i + 1))) = some ((base + 1 + i + 1 : Nat) : Int)
    show some ((base + (i + 1) + 1 : Nat) : Int) = some ((base + 1 + i + 1 : Nat) : Int)
    congr 1
    omega
  · rw [List.getElem?_eq_none_iff.mpr (by rw [List.length_range]; omega), Option.map_none, Option.map_none]

theorem mapM_fresh_cons (r : Role) (rs : List Role) (a : Alloc) :
    ((r :: rs).mapM fresh).run a =
      ((((a.nv + 1 : Nat) : Int) :: ((rs.mapM fresh).run
          { nv := a.nv + 1, roles := a.roles.push r }).1),
        ((rs.mapM fresh).run { nv := a.nv + 1, roles := a.roles.push r }).2) := by
  rw [List.mapM_cons, run_bind, run_bind, run_pure, fresh_run]

theorem roles_push_cons (arr : Array Role) (r : Role) (rs : List Role) :
    (arr.push r) ++ rs.toArray = arr ++ (r :: rs).toArray := by
  rw [List.toArray_cons]
  apply Array.ext'
  simp [Array.toList_append]

theorem freshMany_run (rs : List Role) (a : Alloc) :
    (freshMany rs).run a =
      ((List.range rs.length).map fun i => ((a.nv + i + 1 : Nat) : Int),
        { nv := a.nv + rs.length, roles := a.roles ++ rs.toArray }) := by
  induction rs generalizing a with
  | nil =>
    rw [show (freshMany ([] : List Role)).run a = (([] : List Int), a) from rfl, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    show a = ({ nv := a.nv + [].length, roles := a.roles ++ [].toArray } : Alloc)
    rw [show [].length = 0 from rfl, show a.nv + 0 = a.nv from rfl,
      show ([] : List Role).toArray = #[] from rfl, Array.append_empty]
  | cons r rs ih =>
    rw [show freshMany (r :: rs) = (r :: rs).mapM fresh from rfl, mapM_fresh_cons]
    rw [show (rs.mapM fresh).run { nv := a.nv + 1, roles := a.roles.push r } =
        ((List.range rs.length).map fun i => ((a.nv + 1 + i + 1 : Nat) : Int),
          { nv := a.nv + 1 + rs.length, roles := (a.roles.push r) ++ rs.toArray }) from
      ih { nv := a.nv + 1, roles := a.roles.push r }]
    rw [List.length_cons, map_range_succ, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    show ({ nv := a.nv + 1 + rs.length, roles := (a.roles.push r) ++ rs.toArray } : Alloc) =
      { nv := a.nv + (rs.length + 1), roles := a.roles ++ (r :: rs).toArray }
    rw [roles_push_cons, show a.nv + 1 + rs.length = a.nv + (rs.length + 1) from by omega]

theorem forIn_ext {α β : Type} (l : List α) (b : β) (f : α → β → AM (ForInStep β))
    (h : ∀ a ∈ l, ∀ v, Ext (f a v)) : Ext (forIn l b f) := by
  induction l generalizing b with
  | nil => rw [List.forIn_nil]; exact pure_ext b
  | cons a as ih =>
    rw [List.forIn_cons]
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨h0, h1⟩ := h
    apply bind_ext
    · exact h0 b
    · intro s
      cases s with
      | done b' => exact pure_ext b'
      | yield b' => exact ih b' h1

theorem fresh_role (r : Role) (a : Alloc) (ha : a.roles.size = a.nv) :
    0 < ((fresh r).run a).1 ∧ ((fresh r).run a).2.roles[((fresh r).run a).1.toNat - 1]? = some r := by
  rw [fresh_run]
  refine ⟨by omega, ?_⟩
  show (a.roles.push r)[(((a.nv + 1 : Nat) : Int)).toNat - 1]? = some r
  rw [show (((a.nv + 1 : Nat) : Int)).toNat - 1 = a.nv from by omega, Array.getElem?_push, ← ha, if_pos rfl]

theorem fa2_append_roles (rs : List Role) (pre post : Array Role) (b : Nat) (hb : pre.size = b) :
    Fa2 (fun v r => 0 < v ∧ (pre ++ rs.toArray ++ post)[v.toNat - 1]? = some r)
      ((List.range rs.length).map fun i => ((b + i + 1 : Nat) : Int)) rs := by
  induction rs generalizing pre b with
  | nil => trivial
  | cons r rs ih =>
    rw [List.length_cons, map_range_succ, List.toArray_cons]
    have e : (pre.push r) ++ rs.toArray ++ post = pre ++ (#[r] ++ rs.toArray) ++ post := by
      apply Array.ext'
      simp [Array.toList_append, Array.toList_push]
    rw [← e]
    refine ⟨⟨by omega, ?_⟩, ih (pre.push r) (b + 1) (by rw [Array.size_push]; omega)⟩
    rw [show (((b + 1 : Nat) : Int)).toNat - 1 = b from by omega]
    have hs : (pre.push r).size = b + 1 := by rw [Array.size_push]; omega
    have hs2 : ((pre.push r) ++ rs.toArray).size = b + 1 + rs.length := by
      rw [Array.size_append, hs]
      simp
    rw [Array.getElem?_append_left (by rw [hs2]; omega),
      Array.getElem?_append_left (by rw [hs]; omega), Array.getElem?_push, if_pos hb.symm]

theorem freshMany_roles (rs : List Role) (a : Alloc) (ha : a.roles.size = a.nv) :
    Fa2 (fun v r => 0 < v ∧ ((freshMany rs).run a).2.roles[v.toNat - 1]? = some r) ((freshMany rs).run a).1 rs := by
  rw [freshMany_run rs a]
  have h := fa2_append_roles rs a.roles (#[] : Array Role) a.nv ha
  rw [Array.append_empty] at h
  exact h

theorem role_prefix (a a' : Alloc) (v : Int) (r : Role) (hp : a.roles.toList <+: a'.roles.toList)
    (h : a.roles[v.toNat - 1]? = some r) : a'.roles[v.toNat - 1]? = some r := by
  obtain ⟨rest, hrest⟩ := hp
  rw [← Array.getElem?_toList] at h
  rw [← Array.getElem?_toList, ← hrest]
  obtain ⟨hi, _⟩ := (List.getElem?_eq_some_iff).mp h
  rw [List.getElem?_append_left hi]
  exact h

theorem freshMany_ext (rs : List Role) : Ext (freshMany rs) :=
  mapM_ext rs fresh fun r _ => fresh_ext r

theorem amoAlloc_ext (rs : List Sem) : Ext (amoAlloc rs) := by
  unfold amoAlloc
  split
  · exact pure_ext []
  · exact freshMany_ext _

theorem boardAlloc_ext (g : Cfg) (t : Nat) : Ext (boardAlloc g t) := by
  unfold boardAlloc
  apply bind_ext _ _ ?_ ?_
  · apply forIn_ext
    intro s hs v
    obtain ⟨X, XL⟩ := v
    apply bind_ext _ _ (freshMany_ext _) ?_
    intro xs
    apply bind_ext _ _ (amoAlloc_ext _) ?_
    intro lad
    exact pure_ext _
  · intro z
    obtain ⟨X, XL⟩ := z
    exact pure_ext _

theorem epAlloc_ext (g : Cfg) (t : Nat) : Ext (epAlloc g t) := by
  unfold epAlloc
  apply mapM_ext
  intro s hs
  apply bind_ext _ _ (fresh_ext _) ?_
  intro c
  exact pure_ext _

theorem attAlloc_ext (g : Cfg) (t x : Nat) (X : Array (List Int)) : Ext (attAlloc g t x X) := by
  unfold attAlloc
  apply bind_ext _ _ ?_ ?_
  · apply mapM_ext
    intro ss hss
    apply bind_ext _ _ (fresh_ext _) ?_
    intro c
    exact pure_ext _
  · intro cl
    apply bind_ext _ _ ?_ ?_
    · apply mapM_ext
      rintro ⟨s, conjs⟩ hmem
      apply bind_ext _ _ (fresh_ext _) ?_
      intro av
      apply bind_ext _ _ ?_ ?_
      · apply mapM_ext
        intro conj hc
        split
        · exact pure_ext _
        · apply bind_ext _ _ (fresh_ext _) ?_
          intro cj
          exact pure_ext _
      · intro cs
        exact pure_ext _
    · intro entries
      exact pure_ext _

theorem plyAlloc_ext (g : Cfg) (t : Nat) (E : List (Nat × Int)) : Ext (plyAlloc g t E) := by
  unfold plyAlloc
  apply bind_ext _ _ ?_ ?_
  · apply mapM_ext
    intro s hs
    apply bind_ext _ _ (fresh_ext _) ?_
    intro c
    exact pure_ext _
  · intro fr
    apply bind_ext _ _ ?_ ?_
    · apply mapM_ext
      intro s hs
      apply bind_ext _ _ (fresh_ext _) ?_
      intro c
      exact pure_ext _
    · intro to
      apply bind_ext _ _ (freshMany_ext _) ?_
      intro mp
      apply bind_ext _ _ (freshMany_ext _) ?_
      intro rt
      apply bind_ext _ _ (fresh_ext _) ?_
      intro cap
      apply bind_ext _ _ (fresh_ext _) ?_
      intro promo
      apply bind_ext _ _ (amoAlloc_ext _) ?_
      intro frl
      apply bind_ext _ _ (amoAlloc_ext _) ?_
      intro tol
      apply bind_ext _ _ ?_ ?_
      · apply mapM_ext
        rintro ⟨r, gq, srcs⟩ hmem
        apply bind_ext _ _ (fresh_ext _) ?_
        intro c
        exact pure_ext _
      · intro epr
        apply bind_ext _ _ ?_ ?_
        · apply mapM_ext
          intro s hs
          exact fresh_ext _
        · intro ch
          exact pure_ext _

theorem counterAlloc_ext (g : Cfg) (caps : List Int) : Ext (counterAlloc g caps) := by
  unfold counterAlloc
  split
  · exact pure_ext []
  · apply mapM_ext
    intro i hi
    exact freshMany_ext _

theorem ite_ext {α : Type} (c : Prop) [Decidable c] (x y : AM α) (hx : Ext x) (hy : Ext y) :
    Ext (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]; exact hx
  · rw [if_neg hc]; exact hy

theorem layoutM_ext (g : Cfg) : Ext (layoutM g) := by
  unfold layoutM
  apply bind_ext _ _ ?_ ?_
  · apply forIn_ext
    intro t ht v
    apply bind_ext _ _ (boardAlloc_ext g t) ?_
    rintro ⟨a, b⟩
    exact pure_ext _
  · intro z
    apply bind_ext _ _ ?_ ?_
    · apply forIn_ext
      intro t ht v
      apply bind_ext _ _ (attAlloc_ext g t 0 _) ?_
      intro l0
      apply bind_ext _ _ (attAlloc_ext g t 1 _) ?_
      intro l1
      exact pure_ext _
    · intro z2
      apply bind_ext _ _ (epAlloc_ext g 0) ?_
      intro e0
      apply bind_ext _ _ ?_ ?_
      · apply forIn_ext
        intro t ht v
        apply bind_ext _ _ (plyAlloc_ext g t _) ?_
        intro q
        apply bind_ext _ _ (epAlloc_ext g (t + 1)) ?_
        intro e
        exact pure_ext _
      · intro z3
        apply ite_ext
        · apply bind_ext _ _ (amoAlloc_ext _) ?_
          intro L0
          apply bind_ext _ _ ?_ ?_
          · apply forIn_ext
            intro t ht LS
            apply ite_ext
            · apply bind_ext _ _ (amoAlloc_ext _) ?_
              intro x0
              exact pure_ext _
            · exact pure_ext _
          · intro LS
            apply bind_ext _ _ (counterAlloc_ext g _) ?_
            intro S
            exact pure_ext _
        · apply bind_ext _ _ (pure_ext []) ?_
          intro L0
          apply bind_ext _ _ ?_ ?_
          · apply forIn_ext
            intro t ht LS
            apply ite_ext
            · apply bind_ext _ _ (amoAlloc_ext _) ?_
              intro x0
              exact pure_ext _
            · exact pure_ext _
          · intro LS
            apply bind_ext _ _ (counterAlloc_ext g _) ?_
            intro S
            exact pure_ext _

theorem encodeCfg_alloc (g : Cfg) :
    (encodeCfg g).alloc = ((layoutM g).run { nv := 0, roles := #[] }).2 := by
  unfold encodeCfg
  generalize hr : (layoutM g).run { nv := 0, roles := #[] } = x
  obtain ⟨Ly, a⟩ := x
  rfl

theorem encodeCfg_roles_size (g : Cfg) : (encodeCfg g).alloc.roles.size = (encodeCfg g).alloc.nv := by
  have h := layoutM_ext g { nv := 0, roles := #[] } rfl
  rw [encodeCfg_alloc]
  exact h.1

theorem hasRole_of_prefix (g : Cfg) (a : Alloc) (v : Int) (ro : Role) (hv : 0 < v)
    (hpre : a.roles.toList <+: (encodeCfg g).alloc.roles.toList) (h : a.roles[v.toNat - 1]? = some ro) :
    HasRole (encodeCfg g) v ro :=
  ⟨hv, role_prefix a (encodeCfg g).alloc v ro hpre h⟩

end Alloc



section Roles

variable (g : Cfg)

def attAtL (g : Cfg) (t x : Nat) : AttLayer := (encodeCfg g).layout.att t x

def plyAt (g : Cfg) (t : Nat) : Ply := (encodeCfg g).layout.ply t

namespace X6

def step3 (g : Cfg) (t : Nat) (s : Array (List (Nat × Int)) × Array Ply) :
    AM (Array (List (Nat × Int)) × Array Ply) := do
  let q ← plyAlloc g t (s.1.getD t [])
  let e ← epAlloc g (t + 1)
  pure (s.1.push e, s.2.push q)

def L1 (g : Cfg) : AM (Array (Array (List Int)) × Array (Array (List Int))) :=
  forIn (List.range (g.n + 1)) (#[], #[]) fun (t : Nat) (__s : Array (Array (List Int)) × Array (Array (List Int))) => do
    let __x ← boardAlloc g t
    match __x with
    | (a, b) => pure (.yield (__s.1.push a, __s.2.push b))

def L2 (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int))) : AM (Array (Array AttLayer)) :=
  forIn (List.range (g.n + 1)) (#[] : Array (Array AttLayer)) fun (t : Nat) (__s : Array (Array AttLayer)) => do
    let l0 ← attAlloc g t 0 (XXL.1.getD t #[])
    let l1 ← attAlloc g t 1 (XXL.1.getD t #[])
    pure (.yield (__s.push #[l0, l1]))

def L3 (g : Cfg) (e0 : List (Nat × Int)) : AM (Array (List (Nat × Int)) × Array Ply) :=
  forIn (List.range g.n) (#[e0], #[]) fun (t : Nat) (__s : Array (List (Nat × Int)) × Array Ply) =>
    .yield <$> step3 g t __s

def attRolesOf (AT : Array (Array AttLayer)) (t x : Nat) : List Sem :=
  (((AT.getD t #[]).getD x default).A).map fun (s, _) => Sem.att t x s

def lsStep (g : Cfg) (AT : Array (Array AttLayer)) (t : Nat) (LS : Array (List Int)) : AM (Array (List Int)) :=
  if t + 1 ≤ g.n - 1 then (fun v => LS.push v) <$> amoAlloc (attRolesOf AT (t + 1) (1 - g.col t))
  else pure (LS.push [])

def lsLoop (g : Cfg) (AT : Array (Array AttLayer)) : AM (Array (List Int)) :=
  forIn (List.range g.n) (#[] : Array (List Int)) fun (t : Nat) (LS : Array (List Int)) =>
    if t + 1 ≤ g.n - 1 then (amoAlloc (attRolesOf AT (t + 1) (1 - g.col t)) >>= fun v => pure (.yield (LS.push v)))
    else pure (.yield (LS.push []))

def restAfterL0 (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) (L0 : List Int) : AM Layout :=
  (lsLoop g AT) >>= fun LS =>
  (counterAlloc g (EP.2.toList.map (·.CAP))) >>= fun S =>
  pure { X := XXL.1, XL := XXL.2, AT := AT, EPS := EP.1, PL := EP.2, L0 := L0, LS := LS, S := S.toArray }

def tail (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) : AM Layout := do
  let attRoles := attRolesOf AT
  let L0 ← if g.n ≥ 1 then amoAlloc (attRoles 0 0) else pure []
  let mut LS : Array (List Int) := #[]
  for t in List.range g.n do
    let e := 1 - g.col t
    if t + 1 ≤ g.n - 1 then LS := LS.push (← amoAlloc (attRoles (t + 1) e))
    else LS := LS.push []
  let S ← counterAlloc g (EP.2.toList.map (·.CAP))
  pure { X := XXL.1, XL := XXL.2, AT := AT, EPS := EP.1, PL := EP.2, L0 := L0, LS := LS, S := S.toArray }

theorem run_bind {α β : Type} (x : AM α) (f : α → AM β) (a : Alloc) :
    (x >>= f).run a = (f (x.run a).1).run (x.run a).2 := rfl

theorem run_pure {α : Type} (v : α) (a : Alloc) : (pure v : AM α).run a = (v, a) := rfl

theorem run_map {α β : Type} (f : α → β) (x : AM α) (a : Alloc) :
    (f <$> x).run a = (f (x.run a).1, (x.run a).2) := by
  rw [map_eq_pure_bind, run_bind, run_pure]

theorem layoutM_eq (g : Cfg) :
    layoutM g = (L1 g) >>= fun XXL => (L2 g XXL) >>= fun AT => (epAlloc g 0) >>= fun e0 =>
      (L3 g e0) >>= fun EP => tail g XXL AT EP := rfl

theorem encodeCfg_layout (g : Cfg) :
    (encodeCfg g).layout = ((layoutM g).run { nv := 0, roles := #[] }).1 := rfl

theorem encodeCfg_alloc (g : Cfg) :
    (encodeCfg g).alloc = ((layoutM g).run { nv := 0, roles := #[] }).2 := rfl

theorem forIn_yield {β : Type} (l : List Nat) (step : Nat → β → AM β) (b : β) :
    forIn l b (fun t acc => .yield <$> step t acc) = l.foldlM (fun acc t => step t acc) b := by
  induction l generalizing b with
  | nil => rfl
  | cons t ts ih =>
    rw [List.forIn_cons, List.foldlM_cons, map_eq_pure_bind, bind_assoc]
    congr 1
    funext r
    rw [pure_bind]
    exact ih r

theorem foldlM_range_succ {β : Type} (step : Nat → β → AM β) (k : Nat) (b : β) :
    (List.range (k + 1)).foldlM (fun acc t => step t acc) b =
      ((List.range k).foldlM (fun acc t => step t acc) b) >>= fun b' => step k b' := by
  rw [List.range_succ, List.foldlM_append]
  congr 1

theorem foldlM_ext {β : Type} (l : List Nat) (stp : Nat → β → AM β) (h : ∀ t ∈ l, ∀ b, Ext (stp t b)) (b : β) :
    Ext (l.foldlM (fun acc t => stp t acc) b) := by
  induction l generalizing b with
  | nil => exact pure_ext _
  | cons t ts ih =>
    rw [List.foldlM_cons]
    exact bind_ext _ _ (h t (List.mem_cons_self ..) _) (fun b' => ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) _)

theorem map_ext {α β : Type} (f : α → β) (x : AM α) (hx : Ext x) : Ext (f <$> x) := by
  rw [map_eq_pure_bind]
  exact bind_ext x (fun v => pure (f v)) hx (fun v => pure_ext _)

theorem freshMany_ext (rs : List Role) : Ext (freshMany rs) := by
  intro a ha
  rw [freshMany_run]
  refine ⟨?_, ?_⟩
  · show (a.roles ++ rs.toArray).size = a.nv + rs.length
    rw [Array.size_append, ha, List.size_toArray]
  · show a.roles.toList <+: (a.roles ++ rs.toArray).toList
    rw [Array.toList_append, List.toList_toArray]
    exact List.prefix_append _ _

theorem amoAlloc_ext (rs : List Sem) : Ext (amoAlloc rs) := by
  intro a ha
  rw [amoAlloc]
  split
  · exact pure_ext [] a ha
  · exact freshMany_ext _ a ha

theorem lsStep_ext (g : Cfg) (AT : Array (Array AttLayer)) (t : Nat) (LS : Array (List Int)) :
    Ext (lsStep g AT t LS) := by
  rw [lsStep]
  split
  · exact map_ext _ _ (amoAlloc_ext _)
  · exact pure_ext _

theorem epAlloc_ext (g : Cfg) (t : Nat) : Ext (epAlloc g t) := by
  rw [epAlloc]
  exact mapM_ext _ _ (fun s _ => bind_ext _ _ (fresh_ext _) (fun _ => pure_ext _))

theorem attAlloc_ext (g : Cfg) (t x : Nat) (X : Array (List Int)) : Ext (attAlloc g t x X) := by
  rw [attAlloc]
  apply bind_ext
  · exact mapM_ext _ _ (fun ss _ => bind_ext _ _ (fresh_ext _) (fun _ => pure_ext _))
  · intro cl
    apply bind_ext
    · exact mapM_ext _ _ (fun sc _ => by
        obtain ⟨s, conjs⟩ := sc
        apply bind_ext
        · exact fresh_ext _
        · intro av
          apply bind_ext
          · exact mapM_ext _ _ (fun conj _ => by
              split
              · exact pure_ext _
              · exact bind_ext _ _ (fresh_ext _) (fun _ => pure_ext _))
          · intro cs
            exact pure_ext _)
    · intro entries
      exact pure_ext _

theorem plyAlloc_ext (g : Cfg) (t : Nat) (E : List (Nat × Int)) : Ext (plyAlloc g t E) := by
  rw [plyAlloc]
  apply bind_ext
  · exact mapM_ext _ _ (fun s _ => bind_ext _ _ (fresh_ext _) (fun _ => pure_ext _))
  · intro fr
    apply bind_ext
    · exact mapM_ext _ _ (fun s _ => bind_ext _ _ (fresh_ext _) (fun _ => pure_ext _))
    · intro to
      apply bind_ext
      · exact freshMany_ext _
      · intro mp
        apply bind_ext
        · exact freshMany_ext _
        · intro rt
          apply bind_ext
          · exact fresh_ext _
          · intro cap
            apply bind_ext
            · exact fresh_ext _
            · intro promo
              apply bind_ext
              · exact amoAlloc_ext _
              · intro frl
                apply bind_ext
                · exact amoAlloc_ext _
                · intro tol
                  apply bind_ext
                  · exact mapM_ext _ _ (fun sc _ => by
                      obtain ⟨r, gq, srcs⟩ := sc
                      exact bind_ext _ _ (fresh_ext _) (fun _ => pure_ext _))
                  · intro epr
                    apply bind_ext
                    · exact mapM_ext _ _ (fun s _ => fresh_ext _)
                    · intro ch
                      exact pure_ext _

theorem boardAlloc_ext (g : Cfg) (t : Nat) : Ext (boardAlloc g t) := by
  rw [boardAlloc]
  apply bind_ext
  · apply forIn_ext
    intro s hs sv
    obtain ⟨X, XL⟩ := sv
    apply bind_ext
    · exact freshMany_ext _
    · intro xs
      apply bind_ext
      · exact amoAlloc_ext _
      · intro lad
        exact pure_ext _
  · intro sXXL
    exact pure_ext _

theorem step3_ext (g : Cfg) (t : Nat) (s : Array (List (Nat × Int)) × Array Ply) :
    Ext (step3 g t s) := by
  rw [step3]
  exact bind_ext _ _ (plyAlloc_ext g t (s.1.getD t []))
    (fun q => bind_ext _ _ (epAlloc_ext g (t + 1)) (fun e => pure_ext _))

theorem counterAlloc_ext (g : Cfg) (caps : List Int) : Ext (counterAlloc g caps) := by
  rw [counterAlloc]
  split
  · exact pure_ext []
  · exact mapM_ext _ _ (fun i _ => freshMany_ext _)

theorem L1_ext (g : Cfg) : Ext (L1 g) := by
  rw [L1]
  apply forIn_ext
  intro t ht sv
  apply bind_ext
  · exact boardAlloc_ext g t
  · intro x
    obtain ⟨ab, bb⟩ := x
    exact pure_ext _

theorem L2_ext (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int))) :
    Ext (L2 g XXL) := by
  rw [L2]
  apply forIn_ext
  intro t ht sv
  apply bind_ext
  · exact attAlloc_ext g t 0 _
  · intro l0
    apply bind_ext
    · exact attAlloc_ext g t 1 _
    · intro l1
      exact pure_ext _

theorem L3_ext (g : Cfg) (e0 : List (Nat × Int)) : Ext (L3 g e0) := by
  rw [L3]
  apply forIn_ext
  intro t ht sv
  exact map_ext _ _ (step3_ext g t sv)

theorem lsLoop_ext (g : Cfg) (AT : Array (Array AttLayer)) : Ext (lsLoop g AT) := by
  rw [lsLoop]
  apply forIn_ext
  intro t ht LS
  split
  · exact bind_ext _ _ (amoAlloc_ext _) (fun v => pure_ext _)
  · exact pure_ext _

theorem restAfterL0_ext (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) (L0v : List Int) :
    Ext (restAfterL0 g XXL AT EP L0v) := by
  rw [restAfterL0]
  exact bind_ext _ _ (lsLoop_ext g AT)
    (fun LS => bind_ext _ _ (counterAlloc_ext g _) (fun S => pure_ext _))

theorem pre_ext (g : Cfg) :
    Ext ((L1 g) >>= fun XXL => (L2 g XXL) >>= fun AT => (epAlloc g 0) >>= fun e0 => (L3 g e0)) :=
  bind_ext _ _ (L1_ext g) fun XXL =>
    bind_ext _ _ (L2_ext g XXL) fun AT =>
      bind_ext _ _ (epAlloc_ext g 0) fun e0 => L3_ext g e0

theorem tail_eq_ite (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) :
    tail g XXL AT EP =
      (if g.n ≥ 1 then amoAlloc (attRolesOf AT 0 0) else pure []) >>= fun L0 => restAfterL0 g XXL AT EP L0 := by
  show (ite (g.n ≥ 1) ((amoAlloc (attRolesOf AT 0 0)) >>= fun L0 => restAfterL0 g XXL AT EP L0)
      ((pure ([] : List Int) : AM (List Int)) >>= fun L0 => restAfterL0 g XXL AT EP L0)) = _
  split
  · rfl
  · rfl

theorem tail_eq_ge (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) (h1 : 1 ≤ g.n) :
    tail g XXL AT EP = (amoAlloc (attRolesOf AT 0 0)) >>= fun L0 => restAfterL0 g XXL AT EP L0 := by
  rw [tail_eq_ite, ite_eq_left h1]

theorem rest_L0 (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) (L0v : List Int) :
    ((restAfterL0 g XXL AT EP L0v).run a).1.L0 = L0v := by
  simp only [restAfterL0, run_bind, run_pure]

theorem rest_AT (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) (L0v : List Int) :
    ((restAfterL0 g XXL AT EP L0v).run a).1.AT = AT := by
  simp only [restAfterL0, run_bind, run_pure]

theorem rest_PL (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) (L0v : List Int) :
    ((restAfterL0 g XXL AT EP L0v).run a).1.PL = EP.2 := by
  simp only [restAfterL0, run_bind, run_pure]

theorem rest_LS (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) (L0v : List Int) :
    ((restAfterL0 g XXL AT EP L0v).run a).1.LS = ((lsLoop g AT).run a).1 := by
  simp only [restAfterL0, run_bind, run_pure]

theorem rest_S (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) (L0v : List Int) :
    ((restAfterL0 g XXL AT EP L0v).run a).1.S =
      (((counterAlloc g (EP.2.toList.map (·.CAP))).run ((lsLoop g AT).run a).2).1).toArray := by
  simp only [restAfterL0, run_bind, run_pure]

theorem rest_alloc (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) (L0v : List Int) :
    ((restAfterL0 g XXL AT EP L0v).run a).2 =
      ((counterAlloc g (EP.2.toList.map (·.CAP))).run ((lsLoop g AT).run a).2).2 := by
  simp only [restAfterL0, run_bind, run_pure]

theorem tail_PL (g : Cfg) (XXL : Array (Array (List Int)) × Array (Array (List Int)))
    (AT : Array (Array AttLayer)) (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) :
    ((tail g XXL AT EP).run a).1.PL = EP.2 := by
  by_cases h : g.n ≥ 1
  · rw [tail_eq_ge _ _ _ _ h]; simp only [run_bind, run_pure]
    rw [rest_PL]
  · rw [tail_eq_ite]
    simp only [ite_eq_right (by exact h)]
    rw [run_bind, run_pure]
    rw [rest_PL]

theorem amoAlloc_run_le (rs : List Sem) (σ : Alloc) (h8 : rs.length ≤ 8) :
    (amoAlloc rs).run σ = (([] : List Int), σ) := by
  rw [amoAlloc, ite_eq_left h8]
  rfl

theorem amoAlloc_run_gt (rs : List Sem) (σ : Alloc) (h8 : ¬ rs.length ≤ 8) :
    (amoAlloc rs).run σ =
      ((List.range (rs.length - 1)).map fun i => ((σ.nv + i + 1 : Nat) : Int),
        { nv := σ.nv + (rs.length - 1),
          roles := σ.roles ++ ((List.range (rs.length - 1)).map fun i => Role.ladder rs i).toArray }) := by
  rw [amoAlloc, ite_eq_right h8, freshMany_run]
  simp only [List.length_map, List.length_range]

theorem amoAlloc_roles (rs : List Sem) (σ : Alloc) (hσ : σ.roles.size = σ.nv) (h8 : ¬ rs.length ≤ 8)
    (i : Nat) (hi : i < ((amoAlloc rs).run σ).1.length) :
    0 < ((amoAlloc rs).run σ).1.getD i 0 ∧
    (((amoAlloc rs).run σ).2).roles[(((amoAlloc rs).run σ).1.getD i 0).toNat - 1]? =
      some (.ladder rs i) := by
  rw [amoAlloc_run_gt rs σ h8] at hi ⊢
  simp only [List.length_map, List.length_range] at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some]
  have hv : (List.map (fun j => ((σ.nv + j + 1 : Nat) : Int)) (List.range (rs.length - 1)))[i]'(by simpa using hi) =
      ((σ.nv + i + 1 : Nat) : Int) := by
    simp [List.getElem_map]
  rw [hv]
  constructor
  · exact Int.natCast_pos.mpr (Nat.succ_pos _)
  · have hto : (((σ.nv + i + 1 : Nat) : Int)).toNat - 1 = σ.nv + i := by
      rw [Int.toNat_natCast]; omega
    rw [hto]
    have hL : σ.roles.toList.length = σ.nv := by rw [Array.length_toList, hσ]
    have : (σ.roles ++ ((List.range (rs.length - 1)).map fun j => Role.ladder rs j).toArray)[σ.nv + i]? =
        some (.ladder rs i) := by
      rw [← Array.getElem?_toList, Array.toList_append, List.toList_toArray,
        List.getElem?_append_right (by rw [hL]; exact Nat.le_add_right _ _),
        hL, Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem (by simpa using hi)]
      simp [List.getElem_map, List.getElem_range]
    exact this

theorem amoAlloc_roles2 (rs : List Sem) (σ : Alloc) (hσ : σ.roles.size = σ.nv) (h8 : ¬ rs.length ≤ 8)
    (i : Nat) (hi : i < rs.length - 1) :
    0 < (((List.range (rs.length - 1)).map fun j => ((σ.nv + j + 1 : Nat) : Int)).getD i 0) ∧
    ({ nv := σ.nv + (rs.length - 1),
       roles := σ.roles ++ ((List.range (rs.length - 1)).map fun j => Role.ladder rs j).toArray } : Alloc).roles[
      (((List.range (rs.length - 1)).map fun j => ((σ.nv + j + 1 : Nat) : Int)).getD i 0).toNat - 1]? =
      some (.ladder rs i) := by
  have hrun := amoAlloc_run_gt rs σ h8
  have hlen1 : ((amoAlloc rs).run σ).1.length = rs.length - 1 := by
    rw [hrun]
    simp only [List.length_map, List.length_range]
  obtain ⟨p1, p2⟩ := amoAlloc_roles rs σ hσ h8 i (by rwa [hlen1])
  rw [hrun] at p1 p2
  exact ⟨p1, p2⟩

theorem step3_pl (g : Cfg) (t : Nat) (s : Array (List (Nat × Int)) × Array Ply) (a : Alloc) :
    ((step3 g t s).run a).1.2.size = s.2.size + 1 := by
  simp only [step3, run_bind, run_pure, Array.size_push]

theorem loop3_pl (g : Cfg) (k : Nat) (EPS : Array (List (Nat × Int))) (PL : Array Ply) (a : Alloc) :
    (((List.range k).foldlM (fun acc t => step3 g t acc) (EPS, PL)).run a).1.2.size = PL.size + k := by
  induction k generalizing EPS PL a with
  | zero => rfl
  | succ k ih =>
    rw [foldlM_range_succ, run_bind, step3_pl, ih]
    omega

theorem L3_fold (g : Cfg) (e0 : List (Nat × Int)) :
    L3 g e0 = (List.range g.n).foldlM (fun acc t => step3 g t acc) (#[e0], #[]) := by
  rw [L3, forIn_yield]

theorem decomp (g : Cfg) :
    ∃ XXL AT e0 EP a1 a2 ae aP,
      (L1 g).run { nv := 0, roles := #[] } = (XXL, a1) ∧
      (L2 g XXL).run a1 = (AT, a2) ∧
      (epAlloc g 0).run a2 = (e0, ae) ∧
      (L3 g e0).run ae = (EP, aP) ∧
      aP.roles.size = aP.nv ∧ EP.2.size = g.n := by
  obtain ⟨XXL, a1, h1⟩ : ∃ XXL a1, (L1 g).run { nv := 0, roles := #[] } = (XXL, a1) := ⟨_, _, rfl⟩
  obtain ⟨AT, a2, h2⟩ : ∃ AT a2, (L2 g XXL).run a1 = (AT, a2) := ⟨_, _, rfl⟩
  obtain ⟨e0, ae, he⟩ : ∃ e0 ae, (epAlloc g 0).run a2 = (e0, ae) := ⟨_, _, rfl⟩
  obtain ⟨EP, aP, hp⟩ : ∃ EP aP, (L3 g e0).run ae = (EP, aP) := ⟨_, _, rfl⟩
  refine ⟨XXL, AT, e0, EP, a1, a2, ae, aP, h1, h2, he, hp, ?_, ?_⟩
  · have hx := pre_ext g
    obtain ⟨hsize, _⟩ := hx { nv := 0, roles := #[] } rfl
    have hpr : (((L1 g) >>= fun XXL => (L2 g XXL) >>= fun AT => (epAlloc g 0) >>= fun e0 =>
        (L3 g e0)).run { nv := 0, roles := #[] }) = (EP, aP) := by
      simp only [run_bind, h1, h2, he, hp]
    rw [hpr] at hsize
    exact hsize
  · have h3 := loop3_pl g g.n #[e0] (#[] : Array Ply) ae
    rw [L3_fold] at hp
    rw [hp] at h3
    simpa using h3

theorem PL_size_PL (g : Cfg) : (encodeCfg g).layout.PL.size = g.n := by
  obtain ⟨XXL, AT, e0, EP, a1, a2, ae, aP, h1, h2, he, hp, hs, hpl⟩ := decomp g
  rw [encodeCfg_layout, layoutM_eq]
  simp only [run_bind]
  rw [h1, h2, he, hp, tail_PL, hpl]

theorem getD_map' {α β : Type} (l : List α) (f : α → β) (i : Nat) (d : α) (d0 : β) (h : i < l.length) :
    (l.map f).getD i d0 = f (l.getD i d) := by
  have h2 : i < (l.map f).length := by rwa [List.length_map]
  rw [show (l.map f).getD i d0 = (l.map f)[i]'h2 from (List.getElem_eq_getD _).symm, List.getElem_map,
    show l.getD i d = l[i]'h from (List.getElem_eq_getD _).symm]

theorem arr_getD {α : Type} [Inhabited α] (A : Array α) (i : Nat) (d : α) (h : i < A.size) :
    A.getD i d = A.toList.getD i d := by
  have h2 : i < A.toList.length := by rwa [Array.length_toList]
  rw [show A.getD i d = A[i]'h from (Array.getElem_eq_getD _).symm,
    show A.toList.getD i d = A.toList[i]'h2 from (List.getElem_eq_getD _).symm]
  exact (Array.getElem_toList h2).symm

theorem caps_layout' (g : Cfg) (t : Nat) (ht : t < g.n) :
    ((encodeCfg g).layout.PL.toList.map (·.CAP)).getD t 0 =
      ((encodeCfg g).layout.PL.getD t default).CAP := by
  obtain ⟨XXL, AT, e0, EP, a1, a2, ae, aP, h1, h2, he, hp, hs, hpl⟩ := decomp g
  have hPL : (encodeCfg g).layout.PL = EP.2 := by
    rw [encodeCfg_layout, layoutM_eq]
    simp only [run_bind]
    rw [h1, h2, he, hp, tail_PL]
  rw [hPL]
  have htt : t < EP.2.size := by rwa [hpl]
  rw [getD_map' _ _ _ default 0 (by rwa [Array.length_toList]), ← arr_getD EP.2 t default htt]

theorem rolesX6_L0 (g : Cfg) (h1 : 1 ≤ g.n) :
    let A := (attAtL g 0 0).A
    (8 < A.length → (encodeCfg g).layout.L0.length = A.length - 1) ∧
      ∀ i, i < (encodeCfg g).layout.L0.length → HasRole (encodeCfg g) ((encodeCfg g).layout.L0.getD i 0) (.ladder (A.map fun sa => Sem.att 0 0 sa.1) i) := by
  show (8 < (attAtL g 0 0).A.length → (encodeCfg g).layout.L0.length = (attAtL g 0 0).A.length - 1) ∧
    ∀ i, i < (encodeCfg g).layout.L0.length →
      HasRole (encodeCfg g) ((encodeCfg g).layout.L0.getD i 0) (.ladder ((attAtL g 0 0).A.map fun sa => Sem.att 0 0 sa.1) i)
  obtain ⟨XXL, AT, e0, EP, a1, a2, ae, aP, h1', h2', he', hp', hs', hpl⟩ := decomp g
  obtain ⟨L0v, aL, hA⟩ : ∃ L0v aL, (amoAlloc (attRolesOf AT 0 0)).run aP = (L0v, aL) := ⟨_, _, rfl⟩
  have htg := tail_eq_ge g XXL AT EP h1
  have hL0 : (encodeCfg g).layout.L0 = L0v := by
    rw [encodeCfg_layout, layoutM_eq]
    simp only [run_bind]
    rw [h1', h2', he', hp', htg]
    simp only [run_bind]
    rw [hA, rest_L0]
  have hATf : (encodeCfg g).layout.AT = AT := by
    rw [encodeCfg_layout, layoutM_eq]
    simp only [run_bind]
    rw [h1', h2', he', hp', htg]
    simp only [run_bind]
    rw [hA, rest_AT]
  have hats : attAtL g 0 0 = ((AT.getD 0 #[]).getD 0 default) := by
    rw [attAtL, Layout.att, hATf]
  have hrs : attRolesOf AT 0 0 = (attAtL g 0 0).A.map fun sa => Sem.att 0 0 sa.1 := by
    rw [attRolesOf, hats]
  have halloc : (encodeCfg g).alloc = ((counterAlloc g (EP.2.toList.map (·.CAP))).run ((lsLoop g AT).run aL).2).2 := by
    rw [encodeCfg_alloc, layoutM_eq]
    simp only [run_bind]
    rw [h1', h2', he', hp', htg]
    simp only [run_bind]
    rw [hA, rest_alloc]
  have haL : aL.roles.size = aL.nv := by
    obtain ⟨hsz, _⟩ := amoAlloc_ext _ aP hs'
    rw [hA] at hsz
    exact hsz
  by_cases h8 : (attRolesOf AT 0 0).length ≤ 8
  · have h8A : (attAtL g 0 0).A.length ≤ 8 := by
      have h8c := h8
      rw [hrs, List.length_map] at h8c
      exact h8c
    rw [amoAlloc_run_le _ _ h8] at hA
    obtain ⟨e1, e2⟩ := Prod.mk.inj hA
    subst e1
    subst e2
    constructor
    · intro hgt
      omega
    · intro i hi
      rw [hL0] at hi
      simp at hi
  · constructor
    · intro hgt
      have hlen : L0v.length = (attRolesOf AT 0 0).length - 1 := by
        rw [amoAlloc_run_gt _ _ h8] at hA
        obtain ⟨h1A, -⟩ := (Prod.mk.injEq ..).mp hA
        rw [← h1A]
        simp [List.length_map]
      rw [hL0, hlen, hrs, List.length_map]
    · intro i hi
      rw [hL0] at hi
      obtain ⟨hpos, hrole⟩ := amoAlloc_roles (attRolesOf AT 0 0) aP hs' h8 i (by rw [hA]; exact hi)
      rw [hA] at hpos hrole
      rw [hL0, ← hrs]
      obtain ⟨_, hpre0⟩ := restAfterL0_ext g XXL AT EP L0v aL haL
      rw [rest_alloc, ← halloc] at hpre0
      exact hasRole_of_prefix g aL _ _ hpos hpre0 hrole

theorem lsBody_eq (g : Cfg) (AT : Array (Array AttLayer)) :
    (fun (t : Nat) (LS : Array (List Int)) =>
      (if t + 1 ≤ g.n - 1 then (amoAlloc (attRolesOf AT (t + 1) (1 - g.col t)) >>= fun v => pure (.yield (LS.push v)))
      else pure (.yield (LS.push [])) : AM (ForInStep (Array (List Int))))) =
    fun t LS => (ForInStep.yield <$> lsStep g AT t LS : AM (ForInStep (Array (List Int)))) := by
  funext t LS
  rw [lsStep]
  by_cases h : t + 1 ≤ g.n - 1
  · rw [ite_eq_left h, ite_eq_left h]
    symm
    simp only [map_eq_pure_bind, pure_bind, bind_assoc]
  · rw [ite_eq_right h, ite_eq_right h, map_pure]

theorem lsLoop_fold (g : Cfg) (AT : Array (Array AttLayer)) :
    lsLoop g AT = (List.range g.n).foldlM (fun LS t => lsStep g AT t LS) (#[] : Array (List Int)) := by
  rw [lsLoop, lsBody_eq, forIn_yield]

theorem lsStep_run (g : Cfg) (AT : Array (Array AttLayer)) (t : Nat) (B : Array (List Int)) (a : Alloc)
    (ha : a.roles.size = a.nv) :
    ∃ v a', (lsStep g AT t B).run a = (B.push v, a') ∧ a'.roles.size = a'.nv ∧
      a.roles.toList <+: a'.roles.toList ∧
      (t + 1 ≤ g.n - 1 → (amoAlloc (attRolesOf AT (t + 1) (1 - g.col t))).run a = (v, a')) ∧
      (¬ (t + 1 ≤ g.n - 1) → v = [] ∧ a' = a) := by
  rw [lsStep]
  by_cases ht : t + 1 ≤ g.n - 1
  · rw [ite_eq_left ht, run_map]
    refine ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩
    · exact (amoAlloc_ext (attRolesOf AT (t + 1) (1 - g.col t)) a ha).1
    · exact (amoAlloc_ext (attRolesOf AT (t + 1) (1 - g.col t)) a ha).2
    · intro _
      rfl
    · intro hnx
      exact absurd ht hnx
  · rw [ite_eq_right ht, run_pure]
    exact ⟨[], a, rfl, ha, List.prefix_refl _, fun h => absurd h ht, fun _ => ⟨rfl, rfl⟩⟩

theorem ls_partial (g : Cfg) (AT : Array (Array AttLayer)) (k : Nat) (a : Alloc) (ha : a.roles.size = a.nv) :
    ∃ B a', (((List.range k).foldlM (fun LS t => lsStep g AT t LS) (#[] : Array (List Int))).run a) = (B, a') ∧
      B.size = k ∧ a'.roles.size = a'.nv ∧ a.roles.toList <+: a'.roles.toList := by
  induction k generalizing a with
  | zero => exact ⟨#[], a, rfl, by simp, ha, List.prefix_refl _⟩
  | succ k ih =>
    rw [foldlM_range_succ, run_bind]
    obtain ⟨B, a', hrun, hsz, hnv, hpre⟩ := ih a ha
    rw [hrun]
    obtain ⟨v, a'', hstep, hnv2, hpre2, _, _⟩ := lsStep_run g AT k B a' hnv
    rw [hstep]
    refine ⟨B.push v, a'', rfl, ?_, hnv2, hpre.trans hpre2⟩
    rw [Array.size_push, hsz]

theorem ls_suffix (g : Cfg) (AT : Array (Array AttLayer)) (l : List Nat) (a : Alloc) (B : Array (List Int))
    (ha : a.roles.size = a.nv) :
    ∃ (vs : List (List Int)) (a' : Alloc), ((l.foldlM (fun LS t => lsStep g AT t LS) B).run a) = (B ++ vs.toArray, a') ∧
      vs.length = l.length ∧ a.roles.toList <+: a'.roles.toList ∧ a'.roles.size = a'.nv := by
  induction l generalizing a B with
  | nil =>
    rw [List.foldlM_nil, run_pure]
    exact ⟨([] : List (List Int)), a, by simp, rfl, List.prefix_refl _, ha⟩
  | cons t ts ih =>
    rw [List.foldlM_cons, run_bind]
    obtain ⟨v, a1, hstep, hnv1, hpre1, _, _⟩ := lsStep_run g AT t B a ha
    rw [hstep]
    obtain ⟨vs, a2, h2, hlen, hpre2, hnv2⟩ := ih a1 (B.push v) hnv1
    rw [h2]
    refine ⟨v :: vs, a2, ?_, by simp [hlen], hpre1.trans hpre2, hnv2⟩
    rw [List.toArray_cons, Array.push_eq_append, ← Array.append_assoc]

theorem arr_push_getElem_last {α : Type} (B : Array α) (v : α) (h : B.size < (B.push v).size) :
    (B.push v)[B.size] = v :=
  Array.getElem_push_eq

theorem toArray_getD {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    (l.toArray).getD i d = l.getD i d := by
  have h2 : i < l.toArray.size := by rwa [List.size_toArray]
  rw [show (l.toArray).getD i d = (l.toArray)[i]'h2 from (Array.getElem_eq_getD _).symm,
    List.getElem_toArray, show l.getD i d = l[i]'h from (List.getElem_eq_getD _).symm]

theorem rolesX6_LS (g : Cfg) (t : Nat) (ht : t + 1 ≤ g.n - 1) :
    let e := 1 - g.col t
    let A := (attAtL g (t + 1) e).A
    (8 < A.length → ((encodeCfg g).layout.LS.getD t []).length = A.length - 1) ∧
      ∀ i, i < ((encodeCfg g).layout.LS.getD t []).length →
        HasRole (encodeCfg g) (((encodeCfg g).layout.LS.getD t []).getD i 0)
          (.ladder (A.map fun sa => Sem.att (t + 1) e sa.1) i) := by
  show (8 < (attAtL g (t + 1) (1 - g.col t)).A.length →
      ((encodeCfg g).layout.LS.getD t []).length = (attAtL g (t + 1) (1 - g.col t)).A.length - 1) ∧
    ∀ i, i < ((encodeCfg g).layout.LS.getD t []).length →
      HasRole (encodeCfg g) (((encodeCfg g).layout.LS.getD t []).getD i 0)
        (.ladder ((attAtL g (t + 1) (1 - g.col t)).A.map fun sa => Sem.att (t + 1) (1 - g.col t) sa.1) i)
  have h1 : 1 ≤ g.n := by omega
  obtain ⟨XXL, AT, e0, EP, a1, a2, ae, aP, h1', h2', he', hp', hs', hpl⟩ := decomp g
  obtain ⟨L0v, aL, hA⟩ : ∃ L0v aL, (amoAlloc (attRolesOf AT 0 0)).run aP = (L0v, aL) := ⟨_, _, rfl⟩
  have htg := tail_eq_ge g XXL AT EP h1
  have hATf : (encodeCfg g).layout.AT = AT := by
    rw [encodeCfg_layout, layoutM_eq]
    simp only [run_bind]
    rw [h1', h2', he', hp', htg]
    simp only [run_bind]
    rw [hA, rest_AT]
  have hats : attAtL g (t + 1) (1 - g.col t) = ((AT.getD (t + 1) #[]).getD (1 - g.col t) default) := by
    rw [attAtL, Layout.att, hATf]
  have hrs : attRolesOf AT (t + 1) (1 - g.col t) =
      (attAtL g (t + 1) (1 - g.col t)).A.map fun sa => Sem.att (t + 1) (1 - g.col t) sa.1 := by
    rw [attRolesOf, hats]
  have halloc : (encodeCfg g).alloc = ((counterAlloc g (EP.2.toList.map (·.CAP))).run ((lsLoop g AT).run aL).2).2 := by
    rw [encodeCfg_alloc, layoutM_eq]
    simp only [run_bind]
    rw [h1', h2', he', hp', htg]
    simp only [run_bind]
    rw [hA, rest_alloc]
  have haL : aL.roles.size = aL.nv := by
    obtain ⟨hsz, _⟩ := amoAlloc_ext _ aP hs'
    rw [hA] at hsz
    exact hsz
  have hLSf : (encodeCfg g).layout.LS = ((lsLoop g AT).run aL).1 := by
    rw [encodeCfg_layout, layoutM_eq]
    simp only [run_bind]
    rw [h1', h2', he', hp', htg]
    simp only [run_bind]
    rw [hA, rest_LS]
  obtain ⟨B0, σ0, hrun0, hsz0, hnv0, hpr0⟩ := ls_partial g AT t aL haL
  obtain ⟨v0, σ1, hstep, hnv1, hpr1, hstep_amo, _⟩ := lsStep_run g AT t B0 σ0 hnv0
  have hrange : List.range g.n =
      List.range (t + 1) ++ (List.range (g.n - (t + 1))).map ((t + 1) + ·) := by
    have : g.n = (t + 1) + (g.n - (t + 1)) := by omega
    conv => lhs; rw [this]
    rw [List.range_add]
  have hsplit : (lsLoop g AT).run aL =
      (((List.range (g.n - (t + 1))).map ((t + 1) + ·)).foldlM (fun LS t' => lsStep g AT t' LS)
        (B0.push v0)).run σ1 := by
    have e1 : lsLoop g AT =
        ((List.range (t + 1)).foldlM (fun LS t' => lsStep g AT t' LS) (#[] : Array (List Int))) >>=
          fun B => ((List.range (g.n - (t + 1))).map ((t + 1) + ·)).foldlM (fun LS t' => lsStep g AT t' LS) B := by
      rw [lsLoop_fold, hrange, List.foldlM_append]
    rw [e1, run_bind]
    have hstep0 : ((List.range (t + 1)).foldlM (fun acc t' => lsStep g AT t' acc) (#[] : Array (List Int))).run aL =
        (B0.push v0, σ1) := by
      rw [foldlM_range_succ, run_bind, hrun0, hstep]
    rw [hstep0]
  obtain ⟨vs, aLS, hsuf, hvs, hpr2, hnv2⟩ := ls_suffix g AT ((List.range (g.n - (t + 1))).map ((t + 1) + ·)) σ1 (B0.push v0) hnv1
  rw [hsuf] at hsplit
  have hLSval : (encodeCfg g).layout.LS = ((B0.push v0) ++ vs.toArray) := by
    have hEq := congrArg Prod.fst hsplit
    rw [hLSf]
    exact hEq
  have hget : ((B0.push v0) ++ vs.toArray).getD t [] = v0 := by
    have hL : B0.toList.length = t := by rw [Array.length_toList, hsz0]
    rw [Array.getD_eq_getD_getElem?]
    have hgetElem : ((B0.push v0) ++ vs.toArray)[t]? = some v0 := by
      rw [← Array.getElem?_toList, Array.toList_append, Array.toList_push, List.toList_toArray]
      rw [List.getElem?_append_left (by rw [List.length_append, List.length_cons, List.length_nil, hL]; omega)]
      rw [List.getElem?_append_right (by rw [hL]; exact Nat.le_refl t), hL, Nat.sub_self]
      rfl
    rw [hgetElem]
    rfl
  constructor
  · intro hgt
    have h8 : ¬ (attRolesOf AT (t + 1) (1 - g.col t)).length ≤ 8 := by
      rw [hrs, List.length_map]; exact Nat.not_le_of_gt hgt
    have hAm := hstep_amo ht
    rw [amoAlloc_run_gt _ _ h8] at hAm
    obtain ⟨hv0, -⟩ := Prod.mk.inj hAm
    have hlen : v0.length = (attRolesOf AT (t + 1) (1 - g.col t)).length - 1 := by
      rw [← hv0, List.length_map, List.length_range]
    rw [hLSval, hget, hlen, hrs, List.length_map]
  · intro i hi
    rw [hLSval, hget] at hi ⊢
    rw [← hrs]
    by_cases h8 : (attRolesOf AT (t + 1) (1 - g.col t)).length ≤ 8
    · have hAm := hstep_amo ht
      rw [amoAlloc_run_le _ _ h8] at hAm
      obtain ⟨hv0, -⟩ := Prod.mk.inj hAm
      subst hv0
      simp at hi
    · have hAm := hstep_amo ht
      rw [amoAlloc_run_gt _ _ h8] at hAm
      obtain ⟨p1, p2⟩ := Prod.mk.inj hAm
      subst p2
      subst p1
      obtain ⟨hpos, hrole⟩ := amoAlloc_roles2 (attRolesOf AT (t + 1) (1 - g.col t)) σ0 hnv0 h8 i (by simpa [List.length_map] using hi)
      have hallocF : (encodeCfg g).alloc = ((counterAlloc g (EP.2.toList.map (·.CAP))).run aLS).2 := by
        rw [halloc, hsplit]
      obtain ⟨_, hpreF⟩ := counterAlloc_ext g _ aLS hnv2
      rw [← hallocF] at hpreF
      exact hasRole_of_prefix g _ _ _ hpos (hpr2.trans hpreF) hrole

theorem mapM_range_succ {β : Type} (f : Nat → AM β) (k : Nat) :
    (List.range (k + 1)).mapM f =
      (List.range k).mapM f >>= fun rs => f k >>= fun v => pure (rs ++ [v]) := by
  rw [List.range_succ, List.mapM_append]
  congr 1
def stK (R : Nat → List Role) (a : Alloc) : Nat → Alloc
  | 0 => a
  | i + 1 => { nv := (stK R a i).nv + (R i).length, roles := (stK R a i).roles ++ (R i).toArray }

def rowVals (R : Nat → List Role) (a : Alloc) (i : Nat) : List Int :=
  (List.range (R i).length).map fun j => (((stK R a i).nv + j + 1 : Nat) : Int)

theorem mapM_freshMany_run (R : Nat → List Role) (k : Nat) (a : Alloc) :
    ((List.range k).mapM fun i => freshMany (R i)).run a =
      ((List.range k).map (rowVals R a), stK R a k) := by
  induction k with
  | zero =>
    show ((pure [] : AM (List (List Int))).run a) = ([] , stK R a 0)
    rfl
  | succ k ih =>
    rw [mapM_range_succ]
    simp only [run_bind, run_pure]
    rw [ih, freshMany_run]
    rw [List.range_succ, List.map_append]
    show (((List.range k).map (rowVals R a) ++ [(List.range (R k).length).map fun j =>
            (((stK R a k).nv + j + 1 : Nat) : Int)]),
          { nv := (stK R a k).nv + (R k).length, roles := (stK R a k).roles ++ (R k).toArray }) =
        (((List.range k).map (rowVals R a)) ++ [rowVals R a k], stK R a (k + 1))
    congr 1

theorem counterAlloc_run_ne (g : Cfg) (caps : List Int) (hm : g.m ≠ 0) (a : Alloc) :
    (counterAlloc g caps).run a =
      (((List.range caps.length).mapM fun i =>
        freshMany ((List.range (g.m + 1)).map fun j => Role.count ((List.range g.n).map Sem.cap) i j))).run a := by
  rw [counterAlloc, ite_eq_right hm]

theorem stK_size (R : Nat → List Role) (a : Alloc) (ha : a.roles.size = a.nv) (k : Nat) :
    (stK R a k).roles.size = (stK R a k).nv := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    show ((stK R a k).roles ++ (R k).toArray).size = (stK R a k).nv + (R k).length
    rw [Array.size_append, ih, List.size_toArray]

theorem stK_prefix (R : Nat → List Role) (a : Alloc) (i k : Nat) (h : i ≤ k) :
    (stK R a i).roles.toList <+: (stK R a k).roles.toList := by
  induction k with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact List.prefix_refl _
  | succ k ih =>
    by_cases hik : i = k + 1
    · subst hik; exact List.prefix_refl _
    · have := ih (by omega : i ≤ k)
      refine this.trans ?_
      show (stK R a k).roles.toList <+: ((stK R a k).roles ++ (R k).toArray).toList
      rw [Array.toList_append, List.toList_toArray]
      exact List.prefix_append _ _

theorem rowVal_role (R : Nat → List Role) (a : Alloc) (ha : a.roles.size = a.nv)
    (i j : Nat) (hj : j < (R i).length) :
    0 < (rowVals R a i).getD j 0 ∧
    (stK R a (i + 1)).roles[((rowVals R a i).getD j 0).toNat - 1]? = some ((R i).getD j default) := by
  have hv : (rowVals R a i).getD j 0 = (((stK R a i).nv + j + 1 : Nat) : Int) := by
    rw [rowVals, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [List.length_map] using hj)]
    simp [List.getElem_map, List.getElem_range]
  rw [hv]
  constructor
  · exact Int.natCast_pos.mpr (Nat.succ_pos _)
  · have hto : (((stK R a i).nv + j + 1 : Nat) : Int).toNat - 1 = (stK R a i).nv + j := by
      rw [Int.toNat_natCast]; omega
    rw [hto]
    show ((stK R a i).roles ++ (R i).toArray)[(stK R a i).nv + j]? = some ((R i).getD j default)
    have hsz := stK_size R a ha i
    have hL : (stK R a i).roles.toList.length = (stK R a i).nv := by rw [Array.length_toList, hsz]
    rw [← Array.getElem?_toList, Array.toList_append, List.toList_toArray,
      List.getElem?_append_right (by rw [hL]; exact Nat.le_add_right _ _), hL, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, ← List.getElem_eq_getD]

theorem rolesX6_S (g : Cfg) (h1 : 1 ≤ g.n) (hm : g.m ≠ 0) :
    (encodeCfg g).layout.S.size = g.n ∧ ∀ i, i < g.n → ((encodeCfg g).layout.S.getD i []).length = g.m + 1 ∧
      ∀ j, j < g.m + 1 → HasRole (encodeCfg g) (((encodeCfg g).layout.S.getD i []).getD j 0)
        (.count ((List.range g.n).map Sem.cap) i j) := by
  obtain ⟨XXL, AT, e0, EP, a1, a2, ae, aP, h1', h2', he', hp', hs', hpl⟩ := decomp g
  obtain ⟨L0v, aL, hA⟩ : ∃ L0v aL, (amoAlloc (attRolesOf AT 0 0)).run aP = (L0v, aL) := ⟨_, _, rfl⟩
  obtain ⟨LSv, aLS, hLS⟩ : ∃ LSv aLS, (lsLoop g AT).run aL = (LSv, aLS) := ⟨_, _, rfl⟩
  have htg := tail_eq_ge g XXL AT EP h1
  have haL : aL.roles.size = aL.nv := by
    obtain ⟨hsz, _⟩ := amoAlloc_ext _ aP hs'
    rw [hA] at hsz
    exact hsz
  have hnvLS : aLS.roles.size = aLS.nv := by
    obtain ⟨hsz, _⟩ := lsLoop_ext g AT aL haL
    rw [hLS] at hsz
    exact hsz
  have halloc : (encodeCfg g).alloc =
      ((((List.range (EP.2.toList.map (·.CAP)).length).mapM fun i =>
        freshMany ((List.range (g.m + 1)).map fun j => Role.count ((List.range g.n).map Sem.cap) i j))).run aLS).2 := by
    rw [encodeCfg_alloc, layoutM_eq]
    simp only [run_bind]
    rw [h1', h2', he', hp', htg]
    simp only [run_bind]
    rw [hA, rest_alloc, hLS, counterAlloc_run_ne g (EP.2.toList.map (·.CAP)) hm]
  have hS : (encodeCfg g).layout.S =
      (((((List.range (EP.2.toList.map (·.CAP)).length).mapM fun i =>
        freshMany ((List.range (g.m + 1)).map fun j => Role.count ((List.range g.n).map Sem.cap) i j))).run aLS).1).toArray := by
    rw [encodeCfg_layout, layoutM_eq]
    simp only [run_bind]
    rw [h1', h2', he', hp', htg]
    simp only [run_bind]
    rw [hA, rest_S, hLS, counterAlloc_run_ne g (EP.2.toList.map (·.CAP)) hm]
  have hcaplen : (EP.2.toList.map (·.CAP)).length = g.n := by
    rw [List.length_map, Array.length_toList, hpl]
  have hrun := mapM_freshMany_run (fun i => (List.range (g.m + 1)).map fun j =>
    Role.count ((List.range g.n).map Sem.cap) i j) (EP.2.toList.map (·.CAP)).length aLS
  constructor
  · rw [hS, hrun]
    show (List.toArray ((List.range (EP.2.toList.map (·.CAP)).length).map (rowVals _ aLS))).size = g.n
    rw [List.size_toArray, List.length_map, List.length_range, hcaplen]
  · intro i hi
    have hi' : i < (EP.2.toList.map (·.CAP)).length := by rwa [hcaplen]
    rw [hS, hrun]
    rw [toArray_getD _ _ _ (by rw [List.length_map, List.length_range]; exact hi')]
    rw [show (((List.range (EP.2.toList.map (·.CAP)).length).map (rowVals
        (fun i => (List.range (g.m + 1)).map fun j => Role.count ((List.range g.n).map Sem.cap) i j) aLS)).getD i []) =
        rowVals (fun i => (List.range (g.m + 1)).map fun j => Role.count ((List.range g.n).map Sem.cap) i j) aLS i from by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
        rw [List.length_map, List.length_range]; exact hi')]
      simp [List.getElem_map, List.getElem_range]]
    constructor
    · rw [rowVals]
      simp [List.length_map, List.length_range]
    · intro j hj
      have hjR : j < (((List.range (g.m + 1)).map fun j => Role.count ((List.range g.n).map Sem.cap) i j)).length := by
        simpa [List.length_map] using hj
      obtain ⟨hpos, hrole⟩ := rowVal_role (fun i => (List.range (g.m + 1)).map fun j => Role.count ((List.range g.n).map Sem.cap) i j) aLS hnvLS i j hjR
      have hRj : (List.getD ((List.range (g.m + 1)).map fun j => Role.count ((List.range g.n).map Sem.cap) i j) j default) =
          Role.count ((List.range g.n).map Sem.cap) i j := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjR]
        simp [List.getElem_map, List.getElem_range]
      rw [hRj] at hrole
      have hpre : (stK (fun i => (List.range (g.m + 1)).map fun j => Role.count ((List.range g.n).map Sem.cap) i j) aLS (i + 1)).roles.toList <+: (encodeCfg g).alloc.roles.toList := by
        have h1p := stK_prefix (fun i => (List.range (g.m + 1)).map fun j => Role.count ((List.range g.n).map Sem.cap) i j) aLS (i + 1) (EP.2.toList.map (·.CAP)).length (by omega)
        rw [halloc, hrun]
        exact h1p
      exact hasRole_of_prefix g _ _ _ hpos hpre hrole

end X6
namespace X5

theorem mapIdx_pair_shift {α : Type} (xs : List α) (k : α → Nat) (b : Nat) :
    (xs.mapIdx fun i x => (k x, ((b + (i + 1) + 1 : Nat) : Int))) =
      (xs.mapIdx fun i x => (k x, ((b + 1 + i + 1 : Nat) : Int))) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_mapIdx, List.getElem?_mapIdx]
  cases h : xs[i]? with
  | none => rfl
  | some v =>
    rw [Option.map_some, Option.map_some, show b + (i + 1) + 1 = b + 1 + i + 1 from by omega]

theorem mapIdx_map_fst {α : Type} : ∀ (xs : List α) (k : α → Nat) (f : Nat → Int),
    ((xs.mapIdx fun i x => (k x, f i)).map (·.1)) = xs.map k
  | [], _, _ => rfl
  | x :: xs, k, f => by
      rw [List.mapIdx_cons, List.map_cons, List.map_cons]
      rw [List.cons.injEq]
      exact ⟨rfl, mapIdx_map_fst xs k fun i => f (i + 1)⟩

theorem pair_fresh_gen {α : Type} (xs : List α) (k : α → Nat) (ρ : α → Role) (a : Alloc) :
    (xs.mapM fun x => fresh (ρ x) >>= fun v => pure (k x, v)).run a =
      (xs.mapIdx fun i x => (k x, ((a.nv + i + 1 : Nat) : Int)),
       { nv := a.nv + xs.length, roles := a.roles ++ (xs.map ρ).toArray }) := by
  induction xs generalizing a with
  | nil =>
    rw [List.mapM_nil, run_pure, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    show a = ({ nv := a.nv + [].length, roles := a.roles ++ [].toArray } : Alloc)
    rw [show [].length = 0 from rfl, show a.nv + 0 = a.nv from rfl,
      show ([] : List Role).toArray = #[] from rfl, Array.append_empty]
  | cons x xs ih =>
    have h1 : (((fun x => fresh (ρ x) >>= fun v => pure (k x, v)) x).run a) =
        ((k x, ((a.nv + 1 : Nat) : Int)), { nv := a.nv + 1, roles := a.roles.push (ρ x) }) := by
      show ((fresh (ρ x) >>= fun v => pure (k x, v)).run a) = _
      rw [run_bind, fresh_run, run_pure]
    rw [List.mapM_cons, run_bind, h1, run_bind, ih, run_pure]
    show (((k x, ((a.nv + 1 : Nat) : Int)) ::
        (xs.mapIdx fun i x_1 => (k x_1, ((a.nv + 1 + i + 1 : Nat) : Int))) : List (Nat × Int)),
        ({ nv := a.nv + 1 + xs.length,
           roles := (a.roles.push (ρ x)) ++ (xs.map ρ).toArray } : Alloc)) = _
    rw [List.mapIdx_cons, Prod.mk.injEq, List.cons.injEq]
    refine ⟨⟨rfl, (mapIdx_pair_shift xs k a.nv).symm⟩, ?_⟩
    show ({ nv := a.nv + 1 + xs.length, roles := (a.roles.push (ρ x)) ++ (xs.map ρ).toArray } : Alloc) =
      { nv := a.nv + (x :: xs).length, roles := a.roles ++ ((x :: xs).map ρ).toArray }
    rw [List.map_cons, List.length_cons, roles_push_cons,
      show a.nv + 1 + xs.length = a.nv + (xs.length + 1) from by omega]

theorem mapM_fresh_eq {α : Type} (xs : List α) (ρ : α → Role) :
    (xs.mapM fun x => fresh (ρ x)) = freshMany (xs.map ρ) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, List.map_cons, freshMany, ih]

theorem blk_pos (b i : Nat) : 0 < (((b + i + 1 : Nat)) : Int) := by omega

theorem blk_role2 (a : Alloc) (ha : a.roles.size = a.nv) (rb : List Role) (i : Nat)
    (ro : Role) (hro : rb[i]? = some ro) (σ : Alloc) (hσ : σ.roles = a.roles ++ rb.toArray) :
    σ.roles[(((a.nv + i + 1 : Nat) : Int)).toNat - 1]? = some ro := by
  rw [hσ]
  rw [show (((a.nv + i + 1 : Nat) : Int)).toNat - 1 = a.nv + i from by rw [Int.toNat_natCast]; omega]
  rw [← Array.getElem?_toList, Array.toList_append, List.toList_toArray]
  rw [List.getElem?_append_right (by rw [Array.length_toList, ha]; exact Nat.le_add_right _ _)]
  rw [Array.length_toList, ha, Nat.add_sub_cancel_left, hro]

theorem getD_setIfInBounds_self (A : Array Int) (i : Nat) (v : Int) (h : i < A.size) :
    (A.setIfInBounds i v).getD i 0 = v := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self, if_pos h]
  rfl

theorem getD_setIfInBounds_ne (A : Array Int) (i j : Nat) (v : Int) (h : i ≠ j) :
    (A.setIfInBounds i v).getD j 0 = A.getD j 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_neg h]

theorem foldl_set_other : ∀ (l : List (Nat × Int)) (A : Array Int) (s : Nat),
    s ∉ l.map (·.1) →
    (l.foldl (fun a (s, v) => a.set! s v) A).getD s 0 = A.getD s 0
  | [], A, s, _ => rfl
  | p :: ps, A, s, hmem => by
    obtain ⟨s', v'⟩ := p
    rw [List.foldl_cons, show (match (s', v') with | (s, v) => A.set! s v) = A.setIfInBounds s' v' from rfl]
    rw [foldl_set_other ps _ s (fun h => hmem (List.mem_cons_of_mem _ h))]
    rw [List.map_cons, List.mem_cons] at hmem
    exact getD_setIfInBounds_ne A _ _ _ (fun h => hmem (Or.inl h.symm))

theorem foldl_set_self : ∀ (l : List (Nat × Int)) (A : Array Int) (s : Nat) (v : Int),
    (l.map (·.1)).Nodup → (s, v) ∈ l → s < A.size →
    (l.foldl (fun a (s, v) => a.set! s v) A).getD s 0 = v
  | [], _, _, _, _, hmem, _ => by simp at hmem
  | p :: ps, A, s, v, hnd, hmem, hs => by
    obtain ⟨s', v'⟩ := p
    rw [List.foldl_cons, show (match (s', v') with | (s, v) => A.set! s v) = A.setIfInBounds s' v' from rfl]
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.mem_cons] at hmem
    rcases hmem with heq | htail
    · rw [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [foldl_set_other ps _ s hnd.1, getD_setIfInBounds_self A s v hs]
    · have hs' : s < (A.setIfInBounds s' v').size := by rw [Array.size_setIfInBounds]; exact hs
      exact foldl_set_self ps _ s v hnd.2 htail hs'

theorem toArr_getD (l : List (Nat × Int)) (hnd : (l.map (·.1)).Nodup) (s : Nat) (v : Int)
    (hmem : (s, v) ∈ l) (hs : s < 64) : (toArr l).getD s 0 = v := by
  show (l.foldl (fun a (s, v) => a.set! s v) (Array.replicate 64 0)).getD s 0 = v
  exact foldl_set_self l _ s v hnd hmem (by rw [Array.size_replicate]; exact hs)

theorem NK_length_ge : 62 ≤ g.NK.length := by
  have h62 : 62 ≤ (((List.range 64).erase g.kw).erase g.kb).length :=
    calc 62 = (List.range 64).length - 1 - 1 := by rw [List.length_range]
      _ ≤ ((List.range 64).erase g.kw).length - 1 := Nat.sub_le_sub_right List.le_length_erase 1
      _ ≤ (((List.range 64).erase g.kw).erase g.kb).length := List.le_length_erase
  have hsub : (((List.range 64).erase g.kw).erase g.kb).Sublist g.NK := by
    have s0 : (((List.range 64).erase g.kw).erase g.kb).Sublist (List.range 64) :=
      List.Sublist.trans List.erase_sublist List.erase_sublist
    have hall : ∀ s ∈ (((List.range 64).erase g.kw).erase g.kb), (!g.isK s) = true := by
      intro s hs
      have hnd1 : ((List.range 64).erase g.kw).Nodup := List.nodup_range.erase g.kw
      have h1 := (hnd1.mem_erase_iff).mp hs
      have h2 := (List.nodup_range.mem_erase_iff).mp h1.2
      have e1 : (s == g.kw) = false := by
        cases h : (s == g.kw)
        · rfl
        · exact absurd (beq_iff_eq.mp h) h2.1
      have e2 : (s == g.kb) = false := by
        cases h : (s == g.kb)
        · rfl
        · exact absurd (beq_iff_eq.mp h) h1.1
      show (!(s == g.kw || s == g.kb)) = true
      rw [e1, e2]
      rfl
    show (((List.range 64).erase g.kw).erase g.kb).Sublist ((List.range 64).filter fun s => !g.isK s)
    rw [← List.filter_eq_self.mpr hall]
    exact List.Sublist.filter _ s0
  have hle := List.Sublist.length_le hsub
  omega


def mFR (t : Nat) : AM (List (Nat × Int)) := g.NK.mapM fun s => do return (s, ← fresh (.sem (.fr t s)))

def mTO (t : Nat) : AM (List (Nat × Int)) := g.NK.mapM fun s => do return (s, ← fresh (.sem (.to t s)))

def mMP (t : Nat) : AM (List Int) := freshMany ((List.range 5).map fun p => .sem (.mp t p))

def mRT (t : Nat) : AM (List Int) := freshMany ((List.range 5).map fun p => .sem (.rt t p))

def mCAP (t : Nat) : AM Int := fresh (.sem (.cap t))

def mPROMO (t : Nat) : AM Int := fresh (.sem (.promo t))

def mFRL (t : Nat) : AM (List Int) := amoAlloc (g.NK.map (Sem.fr t))

def mTOL (t : Nat) : AM (List Int) := amoAlloc (g.NK.map (Sem.to t))

def mEPR (t : Nat) (E : List (Nat × Int)) : AM (List (Nat × Int)) :=
  (eprSquares g t E).mapM fun (r, _, _) => do return (r, ← fresh (.sem (.epr t r)))

def mCH (t : Nat) : AM (List Int) := g.NK.mapM fun s => fresh (.sem (.ch t s))

theorem mFR_run (t : Nat) (a : Alloc) :
    (mFR g t).run a =
      (g.NK.mapIdx fun i s => (s, ((a.nv + i + 1 : Nat) : Int)),
       { nv := a.nv + g.NK.length, roles := a.roles ++ (g.NK.map fun s => .sem (.fr t s)).toArray }) :=
  pair_fresh_gen g.NK (fun s => s) (fun s => .sem (.fr t s)) a

theorem mTO_run (t : Nat) (a : Alloc) :
    (mTO g t).run a =
      (g.NK.mapIdx fun i s => (s, ((a.nv + i + 1 : Nat) : Int)),
       { nv := a.nv + g.NK.length, roles := a.roles ++ (g.NK.map fun s => .sem (.to t s)).toArray }) :=
  pair_fresh_gen g.NK (fun s => s) (fun s => .sem (.to t s)) a

theorem mMP_run (t : Nat) (a : Alloc) :
    (mMP t).run a =
      ((List.range 5).map fun i => ((a.nv + i + 1 : Nat) : Int),
       { nv := a.nv + 5, roles := a.roles ++ ((List.range 5).map fun p => .sem (.mp t p)).toArray }) := by
  rw [show mMP t = freshMany ((List.range 5).map fun p => .sem (.mp t p)) from rfl, freshMany_run]
  simp only [List.length_map, List.length_range]

theorem mRT_run (t : Nat) (a : Alloc) :
    (mRT t).run a =
      ((List.range 5).map fun i => ((a.nv + i + 1 : Nat) : Int),
       { nv := a.nv + 5, roles := a.roles ++ ((List.range 5).map fun p => .sem (.rt t p)).toArray }) := by
  rw [show mRT t = freshMany ((List.range 5).map fun p => .sem (.rt t p)) from rfl, freshMany_run]
  simp only [List.length_map, List.length_range]

theorem mCAP_run (t : Nat) (a : Alloc) :
    (mCAP t).run a = (((a.nv + 1 : Nat) : Int), { nv := a.nv + 1, roles := a.roles.push (.sem (.cap t)) }) :=
  fresh_run _ a

theorem mPROMO_run (t : Nat) (a : Alloc) :
    (mPROMO t).run a = (((a.nv + 1 : Nat) : Int), { nv := a.nv + 1, roles := a.roles.push (.sem (.promo t)) }) :=
  fresh_run _ a

theorem mCH_run (t : Nat) (a : Alloc) :
    (mCH g t).run a =
      ((List.range g.NK.length).map fun i => ((a.nv + i + 1 : Nat) : Int),
       { nv := a.nv + g.NK.length, roles := a.roles ++ (g.NK.map fun s => .sem (.ch t s)).toArray }) := by
  rw [show mCH g t = freshMany (g.NK.map fun s => .sem (.ch t s)) from mapM_fresh_eq _ _, freshMany_run]
  simp only [List.length_map]

theorem eprMapM_eq (t : Nat) (l : List (Nat × Nat × List Nat)) :
    (l.mapM fun (r, _, _) => do return (r, ← fresh (.sem (.epr t r)))) =
      ((l.map (·.1)).mapM fun r => do return (r, ← fresh (.sem (.epr t r)))) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨r, gq, srcs⟩ := x
    rw [List.mapM_cons, List.map_cons, List.mapM_cons, ih]

theorem mapIdx_fst_map (l : List (Nat × Nat × List Nat)) (f : Nat → Int) :
    ((l.map (·.1)).mapIdx fun i r => (r, f i)) = l.mapIdx fun i x => (x.1, f i) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_mapIdx, List.getElem?_mapIdx, List.getElem?_map]
  cases h : l[i]? with
  | none => rfl
  | some v => rfl

theorem map_fst_epr (t : Nat) (l : List (Nat × Nat × List Nat)) :
    ((l.map (·.1)).map fun s => Role.sem (Sem.epr t s)) = l.map fun x => Role.sem (Sem.epr t x.1) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨r, gq, srcs⟩ := x
    rw [List.map_cons, List.map_cons, List.map_cons, ih]

theorem mEPR_run (t : Nat) (E : List (Nat × Int)) (a : Alloc) :
    (mEPR g t E).run a =
      ((eprSquares g t E).mapIdx fun i x => (x.1, ((a.nv + i + 1 : Nat) : Int)),
       { nv := a.nv + (eprSquares g t E).length,
         roles := a.roles ++ ((eprSquares g t E).map fun x => .sem (.epr t x.1)).toArray }) := by
  rw [show mEPR g t E = ((eprSquares g t E).map (·.1)).mapM (fun r => do return (r, ← fresh (.sem (.epr t r)))) from
    by rw [show mEPR g t E = (eprSquares g t E).mapM fun (r, _, _) => do return (r, ← fresh (.sem (.epr t r))) from rfl,
      eprMapM_eq]]
  rw [pair_fresh_gen ((eprSquares g t E).map (·.1)) (fun s => s) (fun s => .sem (.epr t s)) a,
    List.length_map, mapIdx_fst_map, map_fst_epr]


theorem mFRL_run (t : Nat) (a : Alloc) (hL : 62 ≤ g.NK.length) :
    (mFRL g t).run a =
      ((List.range (g.NK.length - 1)).map fun i => ((a.nv + i + 1 : Nat) : Int),
       { nv := a.nv + (g.NK.length - 1),
         roles := a.roles ++ ((List.range (g.NK.length - 1)).map fun i =>
           .ladder (g.NK.map (Sem.fr t)) i).toArray }) := by
  have h8 : ¬ (g.NK.map (Sem.fr t)).length ≤ 8 := by rw [List.length_map]; omega
  rw [show mFRL g t = amoAlloc (g.NK.map (Sem.fr t)) from rfl, X6.amoAlloc_run_gt (g.NK.map (Sem.fr t)) a h8]
  simp only [List.length_map]

theorem mTOL_run (t : Nat) (a : Alloc) (hL : 62 ≤ g.NK.length) :
    (mTOL g t).run a =
      ((List.range (g.NK.length - 1)).map fun i => ((a.nv + i + 1 : Nat) : Int),
       { nv := a.nv + (g.NK.length - 1),
         roles := a.roles ++ ((List.range (g.NK.length - 1)).map fun i =>
           .ladder (g.NK.map (Sem.to t)) i).toArray }) := by
  have h8 : ¬ (g.NK.map (Sem.to t)).length ≤ 8 := by rw [List.length_map]; omega
  rw [show mTOL g t = amoAlloc (g.NK.map (Sem.to t)) from rfl, X6.amoAlloc_run_gt (g.NK.map (Sem.to t)) a h8]
  simp only [List.length_map]

theorem epAlloc5_run (t : Nat) (a : Alloc) :
    (epAlloc g t).run a =
      ((epSquares g t).mapIdx fun i s => (s, ((a.nv + i + 1 : Nat) : Int)),
       { nv := a.nv + (epSquares g t).length,
         roles := a.roles ++ ((epSquares g t).map fun s => .sem (.eps t s)).toArray }) :=
  pair_fresh_gen (epSquares g t) (fun s => s) (fun s => .sem (.eps t s)) a

theorem extFR (t : Nat) : Ext (mFR g t) := by
  show Ext (g.NK.mapM fun s => do return (s, ← fresh (.sem (.fr t s))))
  apply mapM_ext
  intro s _
  apply bind_ext _ _ (fresh_ext _)
  intro v
  exact pure_ext _

theorem extTO (t : Nat) : Ext (mTO g t) := by
  show Ext (g.NK.mapM fun s => do return (s, ← fresh (.sem (.to t s))))
  apply mapM_ext
  intro s _
  apply bind_ext _ _ (fresh_ext _)
  intro v
  exact pure_ext _

theorem extMP (t : Nat) : Ext (mMP t) := freshMany_ext _

theorem extRT (t : Nat) : Ext (mRT t) := freshMany_ext _

theorem extCAP (t : Nat) : Ext (mCAP t) := fresh_ext _

theorem extPROMO (t : Nat) : Ext (mPROMO t) := fresh_ext _

theorem extFRL (t : Nat) : Ext (mFRL g t) := amoAlloc_ext _

theorem extTOL (t : Nat) : Ext (mTOL g t) := amoAlloc_ext _

theorem extEPR (t : Nat) (E : List (Nat × Int)) : Ext (mEPR g t E) := by
  show Ext ((eprSquares g t E).mapM fun (r, _, _) => do return (r, ← fresh (.sem (.epr t r))))
  apply mapM_ext
  rintro ⟨r, gq, srcs⟩ hm
  apply bind_ext _ _ (fresh_ext _)
  intro v
  exact pure_ext _

theorem extCH (t : Nat) : Ext (mCH g t) := by
  show Ext (g.NK.mapM fun s => fresh (.sem (.ch t s)))
  apply mapM_ext
  intro s _
  exact fresh_ext _


theorem mFR_val (t : Nat) (a : Alloc) :
    ((mFR g t).run a).1 = g.NK.mapIdx fun i s => (s, ((a.nv + i + 1 : Nat) : Int)) := by
  rw [mFR_run]

theorem mTO_val (t : Nat) (a : Alloc) :
    ((mTO g t).run a).1 = g.NK.mapIdx fun i s => (s, ((a.nv + i + 1 : Nat) : Int)) := by
  rw [mTO_run]

theorem mMP_val (t : Nat) (a : Alloc) :
    ((mMP t).run a).1 = (List.range 5).map fun i => ((a.nv + i + 1 : Nat) : Int) := by
  rw [mMP_run]

theorem mRT_val (t : Nat) (a : Alloc) :
    ((mRT t).run a).1 = (List.range 5).map fun i => ((a.nv + i + 1 : Nat) : Int) := by
  rw [mRT_run]

theorem mCAP_val (t : Nat) (a : Alloc) :
    ((mCAP t).run a).1 = ((a.nv + 1 : Nat) : Int) := by
  rw [mCAP_run]

theorem mPROMO_val (t : Nat) (a : Alloc) :
    ((mPROMO t).run a).1 = ((a.nv + 1 : Nat) : Int) := by
  rw [mPROMO_run]

theorem mFRL_val (t : Nat) (a : Alloc) (hL : 62 ≤ g.NK.length) :
    ((mFRL g t).run a).1 = (List.range (g.NK.length - 1)).map fun i => ((a.nv + i + 1 : Nat) : Int) := by
  rw [mFRL_run g t a hL]

theorem mTOL_val (t : Nat) (a : Alloc) (hL : 62 ≤ g.NK.length) :
    ((mTOL g t).run a).1 = (List.range (g.NK.length - 1)).map fun i => ((a.nv + i + 1 : Nat) : Int) := by
  rw [mTOL_run g t a hL]

theorem mEPR_val (t : Nat) (E : List (Nat × Int)) (a : Alloc) :
    ((mEPR g t E).run a).1 = (eprSquares g t E).mapIdx fun i x => (x.1, ((a.nv + i + 1 : Nat) : Int)) := by
  rw [mEPR_run]

theorem mCH_val (t : Nat) (a : Alloc) :
    ((mCH g t).run a).1 = (List.range g.NK.length).map fun i => ((a.nv + i + 1 : Nat) : Int) := by
  rw [mCH_run]

theorem epAlloc5_val (t : Nat) (a : Alloc) :
    ((epAlloc g t).run a).1 = (epSquares g t).mapIdx fun i s => (s, ((a.nv + i + 1 : Nat) : Int)) := by
  rw [epAlloc5_run]

def a1S : Alloc := ((X6.L1 g).run { nv := 0, roles := #[] }).2

def XXLS := ((X6.L1 g).run { nv := 0, roles := #[] }).1

def a2S : Alloc := ((X6.L2 g (XXLS g)).run (a1S g)).2

def epSt : Nat → Alloc
  | 0 => a2S g
  | t + 1 => ((plyAlloc g t (((epAlloc g t).run (epSt t)).1)).run ((epAlloc g t).run (epSt t)).2).2

def epsVal (t : Nat) : List (Nat × Int) := ((epAlloc g t).run (epSt g t)).1

def pSt (t : Nat) : Alloc := ((epAlloc g t).run (epSt g t)).2

def plVal (t : Nat) : Ply := ((plyAlloc g t (epsVal g t)).run (pSt g t)).1

def plSt (t : Nat) : Alloc := ((plyAlloc g t (epsVal g t)).run (pSt g t)).2

theorem epSt_succ (t : Nat) : epSt g (t + 1) = plSt g t := rfl

theorem st_inv : ∀ t, (epSt g t).roles.size = (epSt g t).nv ∧ (pSt g t).roles.size = (pSt g t).nv := by
  intro t
  induction t with
  | zero =>
    have h1 := X6.L1_ext g { nv := 0, roles := #[] } rfl
    have h2 := X6.L2_ext g (XXLS g) (a1S g) h1.1
    have h0 : (epSt g 0).roles.size = (epSt g 0).nv := h2.1
    refine ⟨h0, ?_⟩
    show ((epAlloc g 0).run (epSt g 0)).2.roles.size = ((epAlloc g 0).run (epSt g 0)).2.nv
    exact (epAlloc_ext g 0 (epSt g 0) h0).1
  | succ t ih =>
    obtain ⟨i1, i2⟩ := ih
    have hp : (epSt g (t + 1)).roles.size = (epSt g (t + 1)).nv := by
      rw [epSt_succ]
      show ((plyAlloc g t (epsVal g t)).run (pSt g t)).2.roles.size =
        ((plyAlloc g t (epsVal g t)).run (pSt g t)).2.nv
      exact (plyAlloc_ext g t (epsVal g t) (pSt g t) i2).1
    refine ⟨hp, ?_⟩
    show ((epAlloc g (t + 1)).run (epSt g (t + 1))).2.roles.size =
      ((epAlloc g (t + 1)).run (epSt g (t + 1))).2.nv
    exact (epAlloc_ext g (t + 1) (epSt g (t + 1)) hp).1

theorem pSt_step (t : Nat) : (pSt g t).roles.toList <+: (pSt g (t + 1)).roles.toList := by
  have h1 := (plyAlloc_ext g t (epsVal g t) (pSt g t) (st_inv g t).2).2
  have h2 := (epAlloc_ext g (t + 1) (epSt g (t + 1)) (st_inv g (t + 1)).1).2
  show (pSt g t).roles.toList <+: (pSt g (t + 1)).roles.toList
  have e1 : ((plyAlloc g t (epsVal g t)).run (pSt g t)).2 = epSt g (t + 1) := (epSt_succ g t).symm
  rw [e1] at h1
  exact h1.trans h2

theorem pSt_chain : ∀ (t k : Nat), (pSt g t).roles.toList <+: (pSt g (t + k)).roles.toList
  | t, 0 => by rw [Nat.add_zero]; exact List.prefix_refl _
  | t, k + 1 => by
    rw [show t + (k + 1) = (t + k) + 1 from by omega]
    exact (pSt_chain t k).trans (pSt_step g (t + k))


def c1S (t : Nat) (a : Alloc) : Alloc := ((mFR g t).run a).2

def c2S (t : Nat) (a : Alloc) : Alloc := ((mTO g t).run (c1S g t a)).2

def c3S (t : Nat) (a : Alloc) : Alloc := ((mMP t).run (c2S g t a)).2

def c4S (t : Nat) (a : Alloc) : Alloc := ((mRT t).run (c3S g t a)).2

def c5S (t : Nat) (a : Alloc) : Alloc := ((mCAP t).run (c4S g t a)).2

def c6S (t : Nat) (a : Alloc) : Alloc := ((mPROMO t).run (c5S g t a)).2

def c7S (t : Nat) (a : Alloc) : Alloc := ((mFRL g t).run (c6S g t a)).2

def c8S (t : Nat) (a : Alloc) : Alloc := ((mTOL g t).run (c7S g t a)).2

def c9S (t : Nat) (E : List (Nat × Int)) (a : Alloc) : Alloc := ((mEPR g t E).run (c8S g t a)).2

def c10S (t : Nat) (E : List (Nat × Int)) (a : Alloc) : Alloc := ((mCH g t).run (c9S g t E a)).2

theorem plyBridge (t : Nat) (E : List (Nat × Int)) (a : Alloc) :
    ((plyAlloc g t E).run a).1 =
      { FR := toArr ((mFR g t).run a).1,
        TO := toArr ((mTO g t).run (c1S g t a)).1,
        MP := ((mMP t).run (c2S g t a)).1,
        RT := ((mRT t).run (c3S g t a)).1,
        CAP := ((mCAP t).run (c4S g t a)).1,
        PROMO := ((mPROMO t).run (c5S g t a)).1,
        FRL := ((mFRL g t).run (c6S g t a)).1,
        TOL := ((mTOL g t).run (c7S g t a)).1,
        EPR := ((mEPR g t E).run (c8S g t a)).1,
        CH := ((mCH g t).run (c9S g t E a)).1 } := rfl

theorem plSt_eq (t : Nat) : plSt g t = c10S g t (epsVal g t) (pSt g t) := rfl

theorem plVal_FR (t : Nat) : (plVal g t).FR = toArr ((mFR g t).run (pSt g t)).1 := rfl

theorem plVal_TO (t : Nat) : (plVal g t).TO = toArr ((mTO g t).run (c1S g t (pSt g t))).1 := rfl

theorem plVal_MP (t : Nat) : (plVal g t).MP = ((mMP t).run (c2S g t (pSt g t))).1 := rfl

theorem plVal_RT (t : Nat) : (plVal g t).RT = ((mRT t).run (c3S g t (pSt g t))).1 := rfl

theorem plVal_CAP (t : Nat) : (plVal g t).CAP = ((mCAP t).run (c4S g t (pSt g t))).1 := rfl

theorem plVal_PROMO (t : Nat) : (plVal g t).PROMO = ((mPROMO t).run (c5S g t (pSt g t))).1 := rfl

theorem plVal_FRL (t : Nat) : (plVal g t).FRL = ((mFRL g t).run (c6S g t (pSt g t))).1 := rfl

theorem plVal_TOL (t : Nat) : (plVal g t).TOL = ((mTOL g t).run (c7S g t (pSt g t))).1 := rfl

theorem plVal_EPR (t : Nat) : (plVal g t).EPR = ((mEPR g t (epsVal g t)).run (c8S g t (pSt g t))).1 := rfl

theorem plVal_CH (t : Nat) : (plVal g t).CH = ((mCH g t).run (c9S g t (epsVal g t) (pSt g t))).1 := rfl

theorem c1S_inv (t : Nat) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c1S g t a).roles.size = (c1S g t a).nv := (extFR g t a ha).1

theorem c2S_inv (t : Nat) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c2S g t a).roles.size = (c2S g t a).nv := (extTO g t (c1S g t a) (c1S_inv g t a ha)).1

theorem c3S_inv (t : Nat) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c3S g t a).roles.size = (c3S g t a).nv := (extMP t (c2S g t a) (c2S_inv g t a ha)).1

theorem c4S_inv (t : Nat) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c4S g t a).roles.size = (c4S g t a).nv := (extRT t (c3S g t a) (c3S_inv g t a ha)).1

theorem c5S_inv (t : Nat) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c5S g t a).roles.size = (c5S g t a).nv := (extCAP t (c4S g t a) (c4S_inv g t a ha)).1

theorem c6S_inv (t : Nat) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c6S g t a).roles.size = (c6S g t a).nv := (extPROMO t (c5S g t a) (c5S_inv g t a ha)).1

theorem c7S_inv (t : Nat) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c7S g t a).roles.size = (c7S g t a).nv := (extFRL g t (c6S g t a) (c6S_inv g t a ha)).1

theorem c8S_inv (t : Nat) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c8S g t a).roles.size = (c8S g t a).nv := (extTOL g t (c7S g t a) (c7S_inv g t a ha)).1

theorem c9S_inv (t : Nat) (E : List (Nat × Int)) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c9S g t E a).roles.size = (c9S g t E a).nv := (extEPR g t E (c8S g t a) (c8S_inv g t a ha)).1
theorem pre1 (t : Nat) (E : List (Nat × Int)) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c1S g t a).roles.toList <+: (c10S g t E a).roles.toList := by
  obtain ⟨h2s, h2p⟩ := extTO g t (c1S g t a) (extFR g t a ha).1
  obtain ⟨h3s, h3p⟩ := extMP t (c2S g t a) h2s
  obtain ⟨h4s, h4p⟩ := extRT t (c3S g t a) h3s
  obtain ⟨h5s, h5p⟩ := extCAP t (c4S g t a) h4s
  obtain ⟨h6s, h6p⟩ := extPROMO t (c5S g t a) h5s
  obtain ⟨h7s, h7p⟩ := extFRL g t (c6S g t a) h6s
  obtain ⟨h8s, h8p⟩ := extTOL g t (c7S g t a) h7s
  obtain ⟨h9s, h9p⟩ := extEPR g t E (c8S g t a) h8s
  obtain ⟨h10s, h10p⟩ := extCH g t (c9S g t E a) h9s
  exact ((((((((h2p.trans h3p).trans h4p).trans h5p).trans h6p).trans h7p).trans h8p).trans h9p).trans h10p)

theorem pre2 (t : Nat) (E : List (Nat × Int)) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c2S g t a).roles.toList <+: (c10S g t E a).roles.toList := by
  obtain ⟨h2s, h2p⟩ := extTO g t (c1S g t a) (extFR g t a ha).1
  obtain ⟨h3s, h3p⟩ := extMP t (c2S g t a) h2s
  obtain ⟨h4s, h4p⟩ := extRT t (c3S g t a) h3s
  obtain ⟨h5s, h5p⟩ := extCAP t (c4S g t a) h4s
  obtain ⟨h6s, h6p⟩ := extPROMO t (c5S g t a) h5s
  obtain ⟨h7s, h7p⟩ := extFRL g t (c6S g t a) h6s
  obtain ⟨h8s, h8p⟩ := extTOL g t (c7S g t a) h7s
  obtain ⟨h9s, h9p⟩ := extEPR g t E (c8S g t a) h8s
  obtain ⟨h10s, h10p⟩ := extCH g t (c9S g t E a) h9s
  exact (((((((h3p.trans h4p).trans h5p).trans h6p).trans h7p).trans h8p).trans h9p).trans h10p)

theorem pre3 (t : Nat) (E : List (Nat × Int)) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c3S g t a).roles.toList <+: (c10S g t E a).roles.toList := by
  obtain ⟨h2s, h2p⟩ := extTO g t (c1S g t a) (extFR g t a ha).1
  obtain ⟨h3s, h3p⟩ := extMP t (c2S g t a) h2s
  obtain ⟨h4s, h4p⟩ := extRT t (c3S g t a) h3s
  obtain ⟨h5s, h5p⟩ := extCAP t (c4S g t a) h4s
  obtain ⟨h6s, h6p⟩ := extPROMO t (c5S g t a) h5s
  obtain ⟨h7s, h7p⟩ := extFRL g t (c6S g t a) h6s
  obtain ⟨h8s, h8p⟩ := extTOL g t (c7S g t a) h7s
  obtain ⟨h9s, h9p⟩ := extEPR g t E (c8S g t a) h8s
  obtain ⟨h10s, h10p⟩ := extCH g t (c9S g t E a) h9s
  exact ((((((h4p.trans h5p).trans h6p).trans h7p).trans h8p).trans h9p).trans h10p)

theorem pre4 (t : Nat) (E : List (Nat × Int)) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c4S g t a).roles.toList <+: (c10S g t E a).roles.toList := by
  obtain ⟨h2s, h2p⟩ := extTO g t (c1S g t a) (extFR g t a ha).1
  obtain ⟨h3s, h3p⟩ := extMP t (c2S g t a) h2s
  obtain ⟨h4s, h4p⟩ := extRT t (c3S g t a) h3s
  obtain ⟨h5s, h5p⟩ := extCAP t (c4S g t a) h4s
  obtain ⟨h6s, h6p⟩ := extPROMO t (c5S g t a) h5s
  obtain ⟨h7s, h7p⟩ := extFRL g t (c6S g t a) h6s
  obtain ⟨h8s, h8p⟩ := extTOL g t (c7S g t a) h7s
  obtain ⟨h9s, h9p⟩ := extEPR g t E (c8S g t a) h8s
  obtain ⟨h10s, h10p⟩ := extCH g t (c9S g t E a) h9s
  exact (((((h5p.trans h6p).trans h7p).trans h8p).trans h9p).trans h10p)

theorem pre5 (t : Nat) (E : List (Nat × Int)) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c5S g t a).roles.toList <+: (c10S g t E a).roles.toList := by
  obtain ⟨h2s, h2p⟩ := extTO g t (c1S g t a) (extFR g t a ha).1
  obtain ⟨h3s, h3p⟩ := extMP t (c2S g t a) h2s
  obtain ⟨h4s, h4p⟩ := extRT t (c3S g t a) h3s
  obtain ⟨h5s, h5p⟩ := extCAP t (c4S g t a) h4s
  obtain ⟨h6s, h6p⟩ := extPROMO t (c5S g t a) h5s
  obtain ⟨h7s, h7p⟩ := extFRL g t (c6S g t a) h6s
  obtain ⟨h8s, h8p⟩ := extTOL g t (c7S g t a) h7s
  obtain ⟨h9s, h9p⟩ := extEPR g t E (c8S g t a) h8s
  obtain ⟨h10s, h10p⟩ := extCH g t (c9S g t E a) h9s
  exact ((((h6p.trans h7p).trans h8p).trans h9p).trans h10p)

theorem pre6 (t : Nat) (E : List (Nat × Int)) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c6S g t a).roles.toList <+: (c10S g t E a).roles.toList := by
  obtain ⟨h2s, h2p⟩ := extTO g t (c1S g t a) (extFR g t a ha).1
  obtain ⟨h3s, h3p⟩ := extMP t (c2S g t a) h2s
  obtain ⟨h4s, h4p⟩ := extRT t (c3S g t a) h3s
  obtain ⟨h5s, h5p⟩ := extCAP t (c4S g t a) h4s
  obtain ⟨h6s, h6p⟩ := extPROMO t (c5S g t a) h5s
  obtain ⟨h7s, h7p⟩ := extFRL g t (c6S g t a) h6s
  obtain ⟨h8s, h8p⟩ := extTOL g t (c7S g t a) h7s
  obtain ⟨h9s, h9p⟩ := extEPR g t E (c8S g t a) h8s
  obtain ⟨h10s, h10p⟩ := extCH g t (c9S g t E a) h9s
  exact (((h7p.trans h8p).trans h9p).trans h10p)

theorem pre7 (t : Nat) (E : List (Nat × Int)) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c7S g t a).roles.toList <+: (c10S g t E a).roles.toList := by
  obtain ⟨h2s, h2p⟩ := extTO g t (c1S g t a) (extFR g t a ha).1
  obtain ⟨h3s, h3p⟩ := extMP t (c2S g t a) h2s
  obtain ⟨h4s, h4p⟩ := extRT t (c3S g t a) h3s
  obtain ⟨h5s, h5p⟩ := extCAP t (c4S g t a) h4s
  obtain ⟨h6s, h6p⟩ := extPROMO t (c5S g t a) h5s
  obtain ⟨h7s, h7p⟩ := extFRL g t (c6S g t a) h6s
  obtain ⟨h8s, h8p⟩ := extTOL g t (c7S g t a) h7s
  obtain ⟨h9s, h9p⟩ := extEPR g t E (c8S g t a) h8s
  obtain ⟨h10s, h10p⟩ := extCH g t (c9S g t E a) h9s
  exact ((h8p.trans h9p).trans h10p)

theorem pre8 (t : Nat) (E : List (Nat × Int)) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c8S g t a).roles.toList <+: (c10S g t E a).roles.toList := by
  obtain ⟨h2s, h2p⟩ := extTO g t (c1S g t a) (extFR g t a ha).1
  obtain ⟨h3s, h3p⟩ := extMP t (c2S g t a) h2s
  obtain ⟨h4s, h4p⟩ := extRT t (c3S g t a) h3s
  obtain ⟨h5s, h5p⟩ := extCAP t (c4S g t a) h4s
  obtain ⟨h6s, h6p⟩ := extPROMO t (c5S g t a) h5s
  obtain ⟨h7s, h7p⟩ := extFRL g t (c6S g t a) h6s
  obtain ⟨h8s, h8p⟩ := extTOL g t (c7S g t a) h7s
  obtain ⟨h9s, h9p⟩ := extEPR g t E (c8S g t a) h8s
  obtain ⟨h10s, h10p⟩ := extCH g t (c9S g t E a) h9s
  exact (h9p.trans h10p)

theorem pre9 (t : Nat) (E : List (Nat × Int)) (a : Alloc) (ha : a.roles.size = a.nv) :
    (c9S g t E a).roles.toList <+: (c10S g t E a).roles.toList := by
  obtain ⟨h2s, h2p⟩ := extTO g t (c1S g t a) (extFR g t a ha).1
  obtain ⟨h3s, h3p⟩ := extMP t (c2S g t a) h2s
  obtain ⟨h4s, h4p⟩ := extRT t (c3S g t a) h3s
  obtain ⟨h5s, h5p⟩ := extCAP t (c4S g t a) h4s
  obtain ⟨h6s, h6p⟩ := extPROMO t (c5S g t a) h5s
  obtain ⟨h7s, h7p⟩ := extFRL g t (c6S g t a) h6s
  obtain ⟨h8s, h8p⟩ := extTOL g t (c7S g t a) h7s
  obtain ⟨h9s, h9p⟩ := extEPR g t E (c8S g t a) h8s
  obtain ⟨h10s, h10p⟩ := extCH g t (c9S g t E a) h9s
  exact h10p


theorem rangeMapArr_getD {β : Type} (f : Nat → β) (d : β) (n t : Nat) (ht : t < n) :
    (((List.range n).map f).toArray).getD t d = f t := by
  rw [Array.getD_eq_getD_getElem?]
  rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_range ht, Option.map_some]
  rfl

theorem mapRange_getD {β : Type} (f : Nat → β) (n i : Nat) (d : β) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_map, List.getElem?_range hi, Option.map_some]
  rfl

theorem rangeMapArr_push {β : Type} (f : Nat → β) (n : Nat) :
    ((((List.range n).map f).toArray).push (f n)) = ((List.range (n + 1)).map f).toArray := by
  rw [List.range_succ, List.map_append, ← List.append_toArray,
    show List.map f [n] = [f n] from rfl, show ([f n]).toArray = #[f n] from rfl, Array.push_eq_append]

theorem map_id_fun {α : Type} : ∀ (l : List α), (l.map fun x => x) = l
  | [] => rfl
  | x :: l => by rw [List.map_cons, map_id_fun l]

theorem NK_nodup : g.NK.Nodup :=
  List.Nodup.sublist List.filter_sublist List.nodup_range

theorem NK_lt (s : Nat) (hs : s ∈ g.NK) : s < 64 :=
  List.mem_range.mp (List.mem_filter.mp hs).1

def ATS := ((X6.L2 g (XXLS g)).run (a1S g)).1

theorem step3_run (t : Nat) (EPS : Array (List (Nat × Int))) (PL : Array Ply)
    (hE : EPS.getD t [] = epsVal g t) :
    (X6.step3 g t (EPS, PL)).run (pSt g t) =
      ((EPS.push (epsVal g (t + 1)), PL.push (plVal g t)), pSt g (t + 1)) := by
  rw [X6.step3]
  have e1 : (EPS, PL).1.getD t [] = epsVal g t := hE
  rw [e1, run_bind, run_bind, run_pure]
  rfl

theorem fold_run : ∀ (k : Nat),
    ((List.range k).foldlM (fun acc t => X6.step3 g t acc) (#[epsVal g 0], #[])).run (pSt g 0) =
      ((((List.range (k + 1)).map (epsVal g)).toArray, ((List.range k).map (plVal g)).toArray), pSt g k)
  | 0 => rfl
  | k + 1 => by
    rw [X6.foldlM_range_succ, run_bind, fold_run k]
    rw [step3_run g k _ _ (rangeMapArr_getD (epsVal g) [] (k + 1) k (by omega))]
    rw [rangeMapArr_push, rangeMapArr_push]

theorem restEPS (XXL : Array (Array (List Int)) × Array (Array (List Int))) (AT : Array (Array AttLayer))
    (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) (L0v : List Int) :
    ((X6.restAfterL0 g XXL AT EP L0v).run a).1.EPS = EP.1 := by
  simp only [X6.restAfterL0, run_bind, run_pure]

theorem tailEPS (XXL : Array (Array (List Int)) × Array (Array (List Int))) (AT : Array (Array AttLayer))
    (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) :
    ((X6.tail g XXL AT EP).run a).1.EPS = EP.1 := by
  by_cases h : g.n ≥ 1
  · rw [X6.tail_eq_ge g XXL AT EP h]
    simp only [run_bind, run_pure]
    rw [restEPS]
  · rw [X6.tail_eq_ite]
    simp only [ite_eq_right h]
    rw [run_bind, run_pure]
    rw [restEPS]

theorem tailExt (XXL : Array (Array (List Int)) × Array (Array (List Int))) (AT : Array (Array AttLayer))
    (EP : Array (List (Nat × Int)) × Array Ply) :
    Ext (X6.tail g XXL AT EP) := by
  rw [X6.tail_eq_ite]
  apply bind_ext _ _ (ite_ext _ _ _ (amoAlloc_ext _) (pure_ext _))
  intro L0
  exact X6.restAfterL0_ext g XXL AT EP L0

theorem bundle :
    (encodeCfg g).layout.EPS = ((List.range (g.n + 1)).map (epsVal g)).toArray ∧
    (encodeCfg g).layout.PL = ((List.range g.n).map (plVal g)).toArray ∧
    (encodeCfg g).alloc = ((X6.tail g (XXLS g) (ATS g)
        ((((List.range (g.n + 1)).map (epsVal g)).toArray), ((List.range g.n).map (plVal g)).toArray)).run
        (pSt g g.n)).2 := by
  obtain ⟨XXL, AT, e0, EP, a1, a2, ae, aP, b1, b2, be, bp, _hsz, hpl⟩ := X6.decomp g
  have hlay : (encodeCfg g).layout = ((X6.tail g XXL AT EP).run aP).1 := by
    rw [X6.encodeCfg_layout, X6.layoutM_eq]
    simp only [run_bind]
    rw [b1, b2, be, bp]
  have hallocF : (encodeCfg g).alloc = ((X6.tail g XXL AT EP).run aP).2 := by
    rw [encodeCfg_alloc, X6.layoutM_eq]
    simp only [run_bind]
    rw [b1, b2, be, bp]
  have hXXL : XXL = XXLS g := (congrArg Prod.fst b1).symm
  have ha1 : a1 = a1S g := (congrArg Prod.snd b1).symm
  rw [hXXL, ha1] at b2
  have hAT : AT = ATS g := (congrArg Prod.fst b2).symm
  have ha2 : a2 = a2S g := (congrArg Prod.snd b2).symm
  have he0 : e0 = epsVal g 0 := by
    have h := (congrArg Prod.fst (ha2 ▸ be)).symm
    exact h
  have hae : ae = pSt g 0 := by
    have h := (congrArg Prod.snd (ha2 ▸ be)).symm
    exact h
  rw [X6.L3_fold] at bp
  rw [he0, hae] at bp
  have hfold := fold_run g g.n
  obtain ⟨hEP, haP⟩ := Prod.mk.inj (hfold.symm.trans bp)
  refine ⟨?_, ?_, ?_⟩
  · rw [hlay, tailEPS, ← hEP]
  · rw [hlay, X6.tail_PL, ← hEP]
  · rw [hallocF, hXXL, hAT, ← hEP, ← haP]

theorem EPSget (t : Nat) (ht : t ≤ g.n) : (encodeCfg g).layout.EPS.getD t [] = epsVal g t := by
  rw [(bundle g).1, rangeMapArr_getD (epsVal g) [] (g.n + 1) t (by omega)]

theorem plyAt_eq (t : Nat) (ht : t < g.n) : plyAt g t = plVal g t := by
  show ((encodeCfg g).layout.PL.getD t default) = plVal g t
  rw [(bundle g).2.1, rangeMapArr_getD (plVal g) default g.n t ht]

theorem pSt_finalN : (pSt g g.n).roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  obtain ⟨hEPS, hPL, halloc⟩ := bundle g
  rw [halloc]
  exact (tailExt g _ _ _ (pSt g g.n) (st_inv g g.n).2).2

theorem pSt_pre_le (t n : Nat) (h : t ≤ n) : (pSt g t).roles.toList <+: (pSt g n).roles.toList := by
  have hh := pSt_chain g t (n - t)
  rw [show t + (n - t) = n from by omega] at hh
  exact hh

theorem pSt_final (t : Nat) (ht : t ≤ g.n) :
    (pSt g t).roles.toList <+: (encodeCfg g).alloc.roles.toList :=
  (pSt_pre_le g t g.n ht).trans (pSt_finalN g)

theorem plSt_final (t : Nat) (ht : t < g.n) :
    (plSt g t).roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  rw [← epSt_succ g t]
  exact ((epAlloc_ext g (t + 1) (epSt g (t + 1)) (st_inv g (t + 1)).1).2).trans
    (pSt_final g (t + 1) (by omega))

theorem fr_pre (t : Nat) (ht : t < g.n) :
    ((mFR g t).run (pSt g t)).2.roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have e : (c1S g t (pSt g t)).roles.toList <+: (plSt g t).roles.toList := by
    rw [plSt_eq]
    exact pre1 g t _ _ (st_inv g t).2
  exact e.trans (plSt_final g t ht)

theorem to_pre (t : Nat) (ht : t < g.n) :
    ((mTO g t).run (c1S g t (pSt g t))).2.roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have e : (c2S g t (pSt g t)).roles.toList <+: (plSt g t).roles.toList := by
    rw [plSt_eq]
    exact pre2 g t _ _ (st_inv g t).2
  exact e.trans (plSt_final g t ht)

theorem mp_pre (t : Nat) (ht : t < g.n) :
    ((mMP t).run (c2S g t (pSt g t))).2.roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have e : (c3S g t (pSt g t)).roles.toList <+: (plSt g t).roles.toList := by
    rw [plSt_eq]
    exact pre3 g t _ _ (st_inv g t).2
  exact e.trans (plSt_final g t ht)

theorem rt_pre (t : Nat) (ht : t < g.n) :
    ((mRT t).run (c3S g t (pSt g t))).2.roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have e : (c4S g t (pSt g t)).roles.toList <+: (plSt g t).roles.toList := by
    rw [plSt_eq]
    exact pre4 g t _ _ (st_inv g t).2
  exact e.trans (plSt_final g t ht)

theorem cap_pre (t : Nat) (ht : t < g.n) :
    ((mCAP t).run (c4S g t (pSt g t))).2.roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have e : (c5S g t (pSt g t)).roles.toList <+: (plSt g t).roles.toList := by
    rw [plSt_eq]
    exact pre5 g t _ _ (st_inv g t).2
  exact e.trans (plSt_final g t ht)

theorem promo_pre (t : Nat) (ht : t < g.n) :
    ((mPROMO t).run (c5S g t (pSt g t))).2.roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have e : (c6S g t (pSt g t)).roles.toList <+: (plSt g t).roles.toList := by
    rw [plSt_eq]
    exact pre6 g t _ _ (st_inv g t).2
  exact e.trans (plSt_final g t ht)

theorem frl_pre (t : Nat) (ht : t < g.n) :
    ((mFRL g t).run (c6S g t (pSt g t))).2.roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have e : (c7S g t (pSt g t)).roles.toList <+: (plSt g t).roles.toList := by
    rw [plSt_eq]
    exact pre7 g t _ _ (st_inv g t).2
  exact e.trans (plSt_final g t ht)

theorem tol_pre (t : Nat) (ht : t < g.n) :
    ((mTOL g t).run (c7S g t (pSt g t))).2.roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have e : (c8S g t (pSt g t)).roles.toList <+: (plSt g t).roles.toList := by
    rw [plSt_eq]
    exact pre8 g t _ _ (st_inv g t).2
  exact e.trans (plSt_final g t ht)

theorem epr_pre (t : Nat) (ht : t < g.n) :
    ((mEPR g t (epsVal g t)).run (c8S g t (pSt g t))).2.roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have e : (c9S g t (epsVal g t) (pSt g t)).roles.toList <+: (plSt g t).roles.toList := by
    rw [plSt_eq]
    exact pre9 g t _ _ (st_inv g t).2
  exact e.trans (plSt_final g t ht)

theorem ch_pre (t : Nat) (ht : t < g.n) :
    ((mCH g t).run (c9S g t (epsVal g t) (pSt g t))).2.roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  show (plSt g t).roles.toList <+: (encodeCfg g).alloc.roles.toList
  exact plSt_final g t ht


theorem mFR_stt (t : Nat) (a : Alloc) :
    ((mFR g t).run a).2 =
      { nv := a.nv + g.NK.length, roles := a.roles ++ (g.NK.map fun s => .sem (.fr t s)).toArray } := by
  rw [mFR_run]

theorem mTO_stt (t : Nat) (a : Alloc) :
    ((mTO g t).run a).2 =
      { nv := a.nv + g.NK.length, roles := a.roles ++ (g.NK.map fun s => .sem (.to t s)).toArray } := by
  rw [mTO_run]

theorem mMP_stt (t : Nat) (a : Alloc) :
    ((mMP t).run a).2 =
      { nv := a.nv + 5, roles := a.roles ++ ((List.range 5).map fun p => .sem (.mp t p)).toArray } := by
  rw [mMP_run]

theorem mRT_stt (t : Nat) (a : Alloc) :
    ((mRT t).run a).2 =
      { nv := a.nv + 5, roles := a.roles ++ ((List.range 5).map fun p => .sem (.rt t p)).toArray } := by
  rw [mRT_run]

theorem mFRL_stt (t : Nat) (a : Alloc) (hL : 62 ≤ g.NK.length) :
    ((mFRL g t).run a).2 =
      { nv := a.nv + (g.NK.length - 1),
        roles := a.roles ++ ((List.range (g.NK.length - 1)).map fun i =>
          .ladder (g.NK.map (Sem.fr t)) i).toArray } := by
  rw [mFRL_run g t a hL]

theorem mTOL_stt (t : Nat) (a : Alloc) (hL : 62 ≤ g.NK.length) :
    ((mTOL g t).run a).2 =
      { nv := a.nv + (g.NK.length - 1),
        roles := a.roles ++ ((List.range (g.NK.length - 1)).map fun i =>
          .ladder (g.NK.map (Sem.to t)) i).toArray } := by
  rw [mTOL_run g t a hL]

theorem mEPR_stt (t : Nat) (E : List (Nat × Int)) (a : Alloc) :
    ((mEPR g t E).run a).2 =
      { nv := a.nv + (eprSquares g t E).length,
        roles := a.roles ++ ((eprSquares g t E).map fun x => .sem (.epr t x.1)).toArray } := by
  rw [mEPR_run]

theorem mCH_stt (t : Nat) (a : Alloc) :
    ((mCH g t).run a).2 =
      { nv := a.nv + g.NK.length, roles := a.roles ++ (g.NK.map fun s => .sem (.ch t s)).toArray } := by
  rw [mCH_run]

theorem epAlloc5_stt (t : Nat) (a : Alloc) :
    ((epAlloc g t).run a).2 =
      { nv := a.nv + (epSquares g t).length,
        roles := a.roles ++ ((epSquares g t).map fun s => .sem (.eps t s)).toArray } := by
  rw [epAlloc5_run]


theorem roles_eps5 (t : Nat) (ht : t ≤ g.n) :
    ((encodeCfg g).layout.EPS.getD t []).map (·.1) = epSquares g t ∧
      ∀ sv ∈ (encodeCfg g).layout.EPS.getD t [], HasRole (encodeCfg g) sv.2 (.sem (.eps t sv.1)) := by
  rw [EPSget g t ht]
  constructor
  · show ((((epAlloc g t).run (epSt g t)).1).map (·.1)) = epSquares g t
    rw [epAlloc5_val g t (epSt g t), mapIdx_map_fst, map_id_fun]
  · intro sv hv
    rw [show epsVal g t = ((epAlloc g t).run (epSt g t)).1 from rfl, epAlloc5_val g t (epSt g t)] at hv
    obtain ⟨i, hi, hsv⟩ := List.mem_iff_getElem.mp hv
    rw [List.length_mapIdx] at hi
    rw [List.getElem_mapIdx] at hsv
    rw [Prod.mk.injEq] at hsv
    rw [← hsv.1, ← hsv.2]
    have hro : ((epSquares g t).map fun s => Role.sem (Sem.eps t s))[i]? =
        some (.sem (.eps t ((epSquares g t)[i]))) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi]
      rfl
    refine hasRole_of_prefix g ((epAlloc g t).run (epSt g t)).2 _ _ (blk_pos _ _) (pSt_final g t ht) ?_
    rw [epAlloc5_stt]
    exact blk_role2 (epSt g t) (st_inv g t).1 _ i _ hro _ rfl

theorem roles_FRTO5 (t s : Nat) (ht : t < g.n) (hs : s ∈ g.NK) :
    HasRole (encodeCfg g) ((plyAt g t).FR.getD s 0) (.sem (.fr t s)) ∧
      HasRole (encodeCfg g) ((plyAt g t).TO.getD s 0) (.sem (.to t s)) := by
  rw [plyAt_eq g t ht]
  obtain ⟨i, hi, hsv⟩ := List.mem_iff_getElem.mp hs
  constructor
  · have hv : (plVal g t).FR.getD s 0 = (((pSt g t).nv + i + 1 : Nat) : Int) := by
      rw [plVal_FR, mFR_val]
      apply toArr_getD
      · rw [mapIdx_map_fst, map_id_fun]
        exact NK_nodup g
      · apply List.mem_iff_getElem.mpr
        refine ⟨i, by rw [List.length_mapIdx]; exact hi, ?_⟩
        rw [List.getElem_mapIdx, hsv]
      · exact NK_lt g s hs
    rw [hv]
    have hro : ((g.NK.map fun s => Role.sem (Sem.fr t s)))[i]? = some (.sem (.fr t s)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi, hsv]
      rfl
    refine hasRole_of_prefix g ((mFR g t).run (pSt g t)).2 _ _ (blk_pos _ _) (fr_pre g t ht) ?_
    rw [mFR_stt]
    exact blk_role2 (pSt g t) (st_inv g t).2 _ i _ hro _ rfl
  · have hv : (plVal g t).TO.getD s 0 = (((c1S g t (pSt g t)).nv + i + 1 : Nat) : Int) := by
      rw [plVal_TO, mTO_val]
      apply toArr_getD
      · rw [mapIdx_map_fst, map_id_fun]
        exact NK_nodup g
      · apply List.mem_iff_getElem.mpr
        refine ⟨i, by rw [List.length_mapIdx]; exact hi, ?_⟩
        rw [List.getElem_mapIdx, hsv]
      · exact NK_lt g s hs
    rw [hv]
    have hro : ((g.NK.map fun s => Role.sem (Sem.to t s)))[i]? = some (.sem (.to t s)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi, hsv]
      rfl
    refine hasRole_of_prefix g ((mTO g t).run (c1S g t (pSt g t))).2 _ _ (blk_pos _ _) (to_pre g t ht) ?_
    rw [mTO_stt]
    exact blk_role2 (c1S g t (pSt g t)) (c1S_inv g t (pSt g t) (st_inv g t).2) _ i _ hro _ rfl


theorem roles_MPRT5 (t : Nat) (ht : t < g.n) :
    (plyAt g t).MP.length = 5 ∧ (plyAt g t).RT.length = 5 ∧
      ∀ p, p < 5 → HasRole (encodeCfg g) ((plyAt g t).MP.getD p 0) (.sem (.mp t p)) ∧
        HasRole (encodeCfg g) ((plyAt g t).RT.getD p 0) (.sem (.rt t p)) := by
  rw [plyAt_eq g t ht]
  refine ⟨?_, ?_, ?_⟩
  · rw [plVal_MP, mMP_val, List.length_map, List.length_range]
  · rw [plVal_RT, mRT_val, List.length_map, List.length_range]
  · intro p hp
    constructor
    · have hv : (plVal g t).MP.getD p 0 = (((c2S g t (pSt g t)).nv + p + 1 : Nat) : Int) := by
        rw [plVal_MP, mMP_val, mapRange_getD _ 5 p 0 hp]
      rw [hv]
      have hro : ((List.range 5).map fun p' => Role.sem (Sem.mp t p'))[p]? = some (.sem (.mp t p)) := by
        rw [List.getElem?_map, List.getElem?_range hp]
        rfl
      refine hasRole_of_prefix g ((mMP t).run (c2S g t (pSt g t))).2 _ _ (blk_pos _ _) (mp_pre g t ht) ?_
      rw [mMP_stt]
      exact blk_role2 (c2S g t (pSt g t)) (c2S_inv g t (pSt g t) (st_inv g t).2) _ p _ hro _ rfl
    · have hv : (plVal g t).RT.getD p 0 = (((c3S g t (pSt g t)).nv + p + 1 : Nat) : Int) := by
        rw [plVal_RT, mRT_val, mapRange_getD _ 5 p 0 hp]
      rw [hv]
      have hro : ((List.range 5).map fun p' => Role.sem (Sem.rt t p'))[p]? = some (.sem (.rt t p)) := by
        rw [List.getElem?_map, List.getElem?_range hp]
        rfl
      refine hasRole_of_prefix g ((mRT t).run (c3S g t (pSt g t))).2 _ _ (blk_pos _ _) (rt_pre g t ht) ?_
      rw [mRT_stt]
      exact blk_role2 (c3S g t (pSt g t)) (c3S_inv g t (pSt g t) (st_inv g t).2) _ p _ hro _ rfl

theorem roles_CAPPROMO5 (t : Nat) (ht : t < g.n) :
    HasRole (encodeCfg g) (plyAt g t).CAP (.sem (.cap t)) ∧
      HasRole (encodeCfg g) (plyAt g t).PROMO (.sem (.promo t)) := by
  rw [plyAt_eq g t ht]
  constructor
  · have hv : (plVal g t).CAP = (((c4S g t (pSt g t)).nv + 1 : Nat) : Int) := by
      rw [plVal_CAP, mCAP_val]
    rw [hv]
    obtain ⟨hpos, hrole⟩ := fresh_role (.sem (.cap t)) (c4S g t (pSt g t))
      (c4S_inv g t (pSt g t) (st_inv g t).2)
    exact hasRole_of_prefix g ((fresh (.sem (.cap t))).run (c4S g t (pSt g t))).2 _ _ hpos
      (cap_pre g t ht) hrole
  · have hv : (plVal g t).PROMO = (((c5S g t (pSt g t)).nv + 1 : Nat) : Int) := by
      rw [plVal_PROMO, mPROMO_val]
    rw [hv]
    obtain ⟨hpos, hrole⟩ := fresh_role (.sem (.promo t)) (c5S g t (pSt g t))
      (c5S_inv g t (pSt g t) (st_inv g t).2)
    exact hasRole_of_prefix g ((fresh (.sem (.promo t))).run (c5S g t (pSt g t))).2 _ _ hpos
      (promo_pre g t ht) hrole

theorem roles_FRTOL5 (t : Nat) (ht : t < g.n) :
    (plyAt g t).FRL.length = g.NK.length - 1 ∧ (plyAt g t).TOL.length = g.NK.length - 1 ∧
      ∀ i, i < g.NK.length - 1 →
        HasRole (encodeCfg g) ((plyAt g t).FRL.getD i 0) (.ladder (g.NK.map (Sem.fr t)) i) ∧
        HasRole (encodeCfg g) ((plyAt g t).TOL.getD i 0) (.ladder (g.NK.map (Sem.to t)) i) := by
  rw [plyAt_eq g t ht]
  obtain hL := NK_length_ge g
  refine ⟨?_, ?_, ?_⟩
  · rw [plVal_FRL, mFRL_val g t _ hL, List.length_map, List.length_range]
  · rw [plVal_TOL, mTOL_val g t _ hL, List.length_map, List.length_range]
  · intro i hi
    constructor
    · have hv : (plVal g t).FRL.getD i 0 = (((c6S g t (pSt g t)).nv + i + 1 : Nat) : Int) := by
        rw [plVal_FRL, mFRL_val g t _ hL, mapRange_getD _ _ i 0 hi]
      rw [hv]
      have hro : (((List.range (g.NK.length - 1)).map fun j => Role.ladder (g.NK.map (Sem.fr t)) j))[i]? =
          some (.ladder (g.NK.map (Sem.fr t)) i) := by
        rw [List.getElem?_map, List.getElem?_range hi]
        rfl
      refine hasRole_of_prefix g ((mFRL g t).run (c6S g t (pSt g t))).2 _ _ (blk_pos _ _) (frl_pre g t ht) ?_
      rw [mFRL_stt g t _ hL]
      exact blk_role2 (c6S g t (pSt g t)) (c6S_inv g t (pSt g t) (st_inv g t).2) _ i _ hro _ rfl
    · have hv : (plVal g t).TOL.getD i 0 = (((c7S g t (pSt g t)).nv + i + 1 : Nat) : Int) := by
        rw [plVal_TOL, mTOL_val g t _ hL, mapRange_getD _ _ i 0 hi]
      rw [hv]
      have hro : (((List.range (g.NK.length - 1)).map fun j => Role.ladder (g.NK.map (Sem.to t)) j))[i]? =
          some (.ladder (g.NK.map (Sem.to t)) i) := by
        rw [List.getElem?_map, List.getElem?_range hi]
        rfl
      refine hasRole_of_prefix g ((mTOL g t).run (c7S g t (pSt g t))).2 _ _ (blk_pos _ _) (tol_pre g t ht) ?_
      rw [mTOL_stt g t _ hL]
      exact blk_role2 (c7S g t (pSt g t)) (c7S_inv g t (pSt g t) (st_inv g t).2) _ i _ hro _ rfl

theorem roles_EPR5 (t : Nat) (ht : t < g.n) :
    (plyAt g t).EPR.map (·.1) = (eprSquares g t ((encodeCfg g).layout.EPS.getD t [])).map (·.1) ∧
      ∀ rv ∈ (plyAt g t).EPR, HasRole (encodeCfg g) rv.2 (.sem (.epr t rv.1)) := by
  rw [plyAt_eq g t ht, EPSget g t (by omega)]
  rw [plVal_EPR, mEPR_val]
  constructor
  · rw [mapIdx_map_fst]
  · intro rv hv
    obtain ⟨i, hi, hrv⟩ := List.mem_iff_getElem.mp hv
    rw [List.length_mapIdx] at hi
    rw [List.getElem_mapIdx] at hrv
    rw [Prod.mk.injEq] at hrv
    rw [← hrv.1, ← hrv.2]
    have hro : ((eprSquares g t (epsVal g t)).map fun x => Role.sem (Sem.epr t x.1))[i]? =
        some (.sem (.epr t ((eprSquares g t (epsVal g t))[i]).1)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi]
      rfl
    refine hasRole_of_prefix g ((mEPR g t (epsVal g t)).run (c8S g t (pSt g t))).2 _ _
      (blk_pos _ _) (epr_pre g t ht) ?_
    rw [mEPR_stt]
    exact blk_role2 (c8S g t (pSt g t)) (c8S_inv g t (pSt g t) (st_inv g t).2) _ i _ hro _ rfl

theorem roles_CH5 (t : Nat) (ht : t < g.n) :
    (plyAt g t).CH.length = g.NK.length ∧
      ∀ i, i < g.NK.length → HasRole (encodeCfg g) ((plyAt g t).CH.getD i 0) (.sem (.ch t (g.NK.getD i 0))) := by
  rw [plyAt_eq g t ht]
  constructor
  · rw [plVal_CH, mCH_val, List.length_map, List.length_range]
  · intro i hi
    have hv : (plVal g t).CH.getD i 0 = (((c9S g t (epsVal g t) (pSt g t)).nv + i + 1 : Nat) : Int) := by
      rw [plVal_CH, mCH_val, mapRange_getD _ _ i 0 hi]
    rw [hv]
    have hro : ((g.NK.map fun s => Role.sem (Sem.ch t s)))[i]? = some (.sem (.ch t (g.NK.getD i 0))) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some]
      congr 1
      congr 1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    refine hasRole_of_prefix g ((mCH g t).run (c9S g t (epsVal g t) (pSt g t))).2 _ _
      (blk_pos _ _) (ch_pre g t ht) ?_
    rw [mCH_stt]
    exact blk_role2 (c9S g t (epsVal g t) (pSt g t)) (c9S_inv g t (epsVal g t) (pSt g t) (st_inv g t).2) _ i _
      hro _ rfl

end X5

namespace X4

def bstep (t s : Nat) (XX : Array (List Int) × Array (List Int)) :
    AM (Array (List Int) × Array (List Int)) :=
  freshMany (((List.range 11).map fun k => Sem.x t s k).map Role.sem) >>= fun xs =>
  amoAlloc ((List.range 11).map fun k => Sem.x t s k) >>= fun lad =>
  pure (XX.1.set! s xs, XX.2.set! s lad)

theorem forIn_yieldB {β : Type} (l : List Nat) (step : Nat → β → AM β) (b : β) :
    forIn l b (fun t acc => step t acc >>= fun r => pure (ForInStep.yield r)) =
      l.foldlM (fun acc t => step t acc) b := by
  induction l generalizing b with
  | nil => rfl
  | cons t ts ih =>
    rw [List.forIn_cons, List.foldlM_cons, bind_assoc]
    congr 1
    funext r
    rw [pure_bind]
    exact ih r

theorem boardAlloc_eq (t : Nat) :
    boardAlloc g t = (g.NK.foldlM (fun acc s => bstep t s acc) (Array.replicate 64 [], Array.replicate 64 []))
      >>= fun r => pure (r.1, r.2) := by
  rw [← forIn_yieldB]
  unfold boardAlloc bstep
  simp only [bind_assoc, pure_bind]

def xsv (a : Alloc) : List Int := (List.range 11).map fun i => ((a.nv + i + 1 : Nat) : Int)

def ladv (a : Alloc) : List Int := (List.range 10).map fun i => ((a.nv + 11 + i + 1 : Nat) : Int)

def xrs (t s : Nat) : List Sem := (List.range 11).map (Sem.x t s)

def bA (t s : Nat) (a : Alloc) : Alloc :=
  { nv := a.nv + 11 + 10,
    roles := a.roles ++ ((xrs t s).map Role.sem).toArray ++ ((List.range 10).map (Role.ladder (xrs t s))).toArray }

theorem bstep_run (t s : Nat) (XX : Array (List Int) × Array (List Int)) (a : Alloc) :
    (bstep t s XX).run a = ((XX.1.set! s (xsv a), XX.2.set! s (ladv a)), bA t s a) := by
  unfold bstep
  rw [X6.run_bind, freshMany_run, X6.run_bind, X6.amoAlloc_run_gt _ _ (by simp)]
  simp only [List.length_map, List.length_range]
  rfl


def GoodB (a : Alloc) (t s : Nat) (XX : Array (List Int) × Array (List Int)) : Prop :=
  (∀ k, k < 11 → 0 < xv XX.1 s k ∧ a.roles[(xv XX.1 s k).toNat - 1]? = some (.sem (.x t s k))) ∧
  (XX.2.getD s []).length = 10 ∧
  ∀ i, i < 10 → 0 < (XX.2.getD s []).getD i 0 ∧
    a.roles[((XX.2.getD s []).getD i 0).toNat - 1]? = some (.ladder (xrs t s) i)

theorem goodB_congr (a a' : Alloc) (t s : Nat) (XX XX' : Array (List Int) × Array (List Int))
    (hp : a.roles.toList <+: a'.roles.toList) (h1 : XX'.1.getD s [] = XX.1.getD s [])
    (h2 : XX'.2.getD s [] = XX.2.getD s []) (h : GoodB a t s XX) : GoodB a' t s XX' := by
  obtain ⟨hx, hl, hL⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have e : xv XX'.1 s k = xv XX.1 s k := by
      show (XX'.1.getD s []).getD k 0 = (XX.1.getD s []).getD k 0
      rw [h1]
    rw [e]
    exact ⟨(hx k hk).1, role_prefix a a' _ _ hp (hx k hk).2⟩
  · rw [h2]; exact hl
  · intro i hi
    rw [h2]
    exact ⟨(hL i hi).1, role_prefix a a' _ _ hp (hL i hi).2⟩

theorem arr_set_getD_self (A : Array (List Int)) (i : Nat) (v : List Int) (h : i < A.size) :
    (A.set! i v).getD i [] = v := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self, ite_eq_left h]
  rfl

theorem arr_set_getD_ne (A : Array (List Int)) (i j : Nat) (v : List Int) (h : i ≠ j) :
    (A.set! i v).getD j [] = A.getD j [] := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, ite_eq_right h]

theorem bA_inv (t s : Nat) (a : Alloc) (ha : a.roles.size = a.nv) : (bA t s a).roles.size = (bA t s a).nv := by
  simp [bA, xrs, ha]

theorem bA_pre (t s : Nat) (a : Alloc) : a.roles.toList <+: (bA t s a).roles.toList := by
  simp only [bA, Array.toList_append, List.append_assoc]
  exact List.prefix_append _ _

theorem bstep_good (t s : Nat) (XX : Array (List Int) × Array (List Int)) (a : Alloc) (ha : a.roles.size = a.nv)
    (h1 : s < XX.1.size) (h2 : s < XX.2.size) :
    GoodB (bA t s a) t s (XX.1.set! s (xsv a), XX.2.set! s (ladv a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have e : xv (XX.1.set! s (xsv a)) s k = ((a.nv + k + 1 : Nat) : Int) := by
      show ((XX.1.set! s (xsv a)).getD s []).getD k 0 = _
      rw [arr_set_getD_self _ _ _ h1, xsv, X5.mapRange_getD _ _ _ _ hk]
    rw [e]
    refine ⟨X5.blk_pos _ _, ?_⟩
    have hro : ((xrs t s).map Role.sem)[k]? = some (.sem (.x t s k)) := by
      rw [List.getElem?_map, xrs, List.getElem?_map, List.getElem?_range hk]
      rfl
    have hσ : ({ nv := a.nv + 11, roles := a.roles ++ ((xrs t s).map Role.sem).toArray } : Alloc).roles =
        a.roles ++ ((xrs t s).map Role.sem).toArray := rfl
    have := X5.blk_role2 a ha _ k _ hro _ hσ
    exact role_prefix _ (bA t s a) _ _ (by
      show (a.roles ++ ((xrs t s).map Role.sem).toArray).toList <+: _
      simp only [bA, Array.toList_append]
      exact List.prefix_append _ _) this
  · show ((XX.2.set! s (ladv a)).getD s []).length = 10
    rw [arr_set_getD_self _ _ _ h2, ladv, List.length_map, List.length_range]
  · intro i hi
    show 0 < ((XX.2.set! s (ladv a)).getD s []).getD i 0 ∧
      (bA t s a).roles[(((XX.2.set! s (ladv a)).getD s []).getD i 0).toNat - 1]? = _
    rw [arr_set_getD_self _ _ _ h2, ladv, X5.mapRange_getD _ _ _ _ hi]
    refine ⟨X5.blk_pos _ _, ?_⟩
    have hro : ((List.range 10).map (Role.ladder (xrs t s)))[i]? = some (.ladder (xrs t s) i) := by
      rw [List.getElem?_map, List.getElem?_range hi]
      rfl
    have ha' : (a.roles ++ ((xrs t s).map Role.sem).toArray).size = a.nv + 11 := by
      simp [xrs, ha]
    exact X5.blk_role2 { nv := a.nv + 11, roles := a.roles ++ ((xrs t s).map Role.sem).toArray } ha' _ i _ hro _ rfl


def bres (t : Nat) (l : List Nat) (XX : Array (List Int) × Array (List Int)) (a : Alloc) :
    (Array (List Int) × Array (List Int)) × Alloc :=
  (l.foldlM (fun acc s => bstep t s acc) XX).run a

theorem bres_cons (t s : Nat) (l : List Nat) (XX : Array (List Int) × Array (List Int)) (a : Alloc) :
    bres t (s :: l) XX a = bres t l (XX.1.set! s (xsv a), XX.2.set! s (ladv a)) (bA t s a) := by
  unfold bres
  rw [List.foldlM_cons, X6.run_bind, bstep_run]

theorem bloop (t : Nat) : ∀ (l : List Nat) (XX : Array (List Int) × Array (List Int)) (a : Alloc),
    a.roles.size = a.nv → l.Nodup → (∀ s ∈ l, s < XX.1.size ∧ s < XX.2.size) →
    (bres t l XX a).2.roles.size = (bres t l XX a).2.nv ∧
    a.roles.toList <+: (bres t l XX a).2.roles.toList ∧
    (bres t l XX a).1.1.size = XX.1.size ∧ (bres t l XX a).1.2.size = XX.2.size ∧
    (∀ s, s ∉ l → (bres t l XX a).1.1.getD s [] = XX.1.getD s [] ∧
      (bres t l XX a).1.2.getD s [] = XX.2.getD s []) ∧
    ∀ s ∈ l, GoodB (bres t l XX a).2 t s (bres t l XX a).1
  | [], XX, a, ha, _, _ => ⟨ha, List.prefix_refl _, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩,
      fun _ h => absurd h List.not_mem_nil⟩
  | s :: l, XX, a, ha, hnd, hsz => by
    rw [bres_cons]
    obtain ⟨hs0, hl⟩ := List.nodup_cons.mp hnd
    have hsz0 := hsz s List.mem_cons_self
    have e1 : (XX.1.set! s (xsv a)).size = XX.1.size := by simp
    have e2 : (XX.2.set! s (ladv a)).size = XX.2.size := by simp
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := bloop t l (XX.1.set! s (xsv a), XX.2.set! s (ladv a)) (bA t s a)
      (bA_inv t s a ha) hl (fun s' hs' => by
        show s' < (XX.1.set! s (xsv a)).size ∧ s' < (XX.2.set! s (ladv a)).size
        rw [e1, e2]; exact hsz s' (List.mem_cons_of_mem _ hs'))
    refine ⟨i1, (bA_pre t s a).trans i2, i3.trans e1, i4.trans e2, ?_, ?_⟩
    · intro s' hs'
      have hne : s ≠ s' := fun h => hs' (h ▸ List.mem_cons_self)
      have hn' : s' ∉ l := fun h => hs' (List.mem_cons_of_mem _ h)
      obtain ⟨j1, j2⟩ := i5 s' hn'
      refine ⟨j1.trans (arr_set_getD_ne _ _ _ _ hne), j2.trans (arr_set_getD_ne _ _ _ _ hne)⟩
    · intro s' hs'
      rcases List.mem_cons.mp hs' with h | h
      · subst h
        obtain ⟨j1, j2⟩ := i5 s' hs0
        exact goodB_congr _ _ t s' _ _ i2 j1 j2 (bstep_good t s' XX a ha hsz0.1 hsz0.2)
      · exact i6 s' h


def rep64 : Array (List Int) × Array (List Int) := (Array.replicate 64 [], Array.replicate 64 [])

theorem boardAlloc_run (t : Nat) (a : Alloc) :
    (boardAlloc g t).run a = (((bres t g.NK rep64 a).1.1, (bres t g.NK rep64 a).1.2), (bres t g.NK rep64 a).2) := by
  rw [boardAlloc_eq, X6.run_bind]
  rfl

def step1 (t : Nat) (acc : Array (Array (List Int)) × Array (Array (List Int))) :
    AM (Array (Array (List Int)) × Array (Array (List Int))) :=
  boardAlloc g t >>= fun ab => pure (acc.1.push ab.1, acc.2.push ab.2)

theorem L1_fold : X6.L1 g = (List.range (g.n + 1)).foldlM (fun acc t => step1 g t acc) (#[], #[]) := by
  rw [← forIn_yieldB]
  unfold X6.L1 step1
  simp only [bind_assoc, pure_bind]

def bSt : Nat → Alloc
  | 0 => { nv := 0, roles := #[] }
  | t + 1 => ((boardAlloc g t).run (bSt t)).2

def bVal (t : Nat) : Array (List Int) × Array (List Int) := ((boardAlloc g t).run (bSt g t)).1

theorem fold1_run : ∀ (k : Nat),
    ((List.range k).foldlM (fun acc t => step1 g t acc) (#[], #[])).run { nv := 0, roles := #[] } =
      ((((List.range k).map fun t => (bVal g t).1).toArray, ((List.range k).map fun t => (bVal g t).2).toArray),
        bSt g k)
  | 0 => rfl
  | k + 1 => by
    rw [X6.foldlM_range_succ, X6.run_bind, fold1_run k]
    unfold step1
    rw [X6.run_bind, X6.run_pure]
    show (((((List.range k).map fun t => (bVal g t).1).toArray.push (bVal g k).1,
      ((List.range k).map fun t => (bVal g t).2).toArray.push (bVal g k).2)), bSt g (k + 1)) = _
    rw [X5.rangeMapArr_push (fun t => (bVal g t).1), X5.rangeMapArr_push (fun t => (bVal g t).2)]

theorem XXLS_eq : X5.XXLS g = (((List.range (g.n + 1)).map fun t => (bVal g t).1).toArray,
    ((List.range (g.n + 1)).map fun t => (bVal g t).2).toArray) := by
  unfold X5.XXLS
  rw [L1_fold, fold1_run]

theorem a1S_eq : X5.a1S g = bSt g (g.n + 1) := by
  unfold X5.a1S
  rw [L1_fold, fold1_run]

theorem bSt_inv : ∀ t, (bSt g t).roles.size = (bSt g t).nv
  | 0 => rfl
  | t + 1 => (boardAlloc_ext g t (bSt g t) (bSt_inv t)).1

theorem bSt_step (t : Nat) : (bSt g t).roles.toList <+: (bSt g (t + 1)).roles.toList :=
  (boardAlloc_ext g t (bSt g t) (bSt_inv g t)).2

theorem bSt_chain : ∀ (t k : Nat), (bSt g t).roles.toList <+: (bSt g (t + k)).roles.toList
  | t, 0 => by rw [Nat.add_zero]; exact List.prefix_refl _
  | t, k + 1 => by
    rw [show t + (k + 1) = (t + k) + 1 from by omega]
    exact (bSt_chain t k).trans (bSt_step g (t + k))

theorem a1S_final : (X5.a1S g).roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have h1 := X6.L1_ext g { nv := 0, roles := #[] } rfl
  have h2 := X6.L2_ext g (X5.XXLS g) (X5.a1S g) h1.1
  have h3 : (X5.epSt g 0).roles.toList <+: (X5.pSt g 0).roles.toList :=
    (epAlloc_ext g 0 (X5.epSt g 0) h2.1).2
  exact h2.2.trans (h3.trans (X5.pSt_final g 0 (Nat.zero_le _)))

theorem bSt_final (t : Nat) (ht : t ≤ g.n) :
    (bSt g (t + 1)).roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have h := bSt_chain g (t + 1) (g.n - t)
  rw [show t + 1 + (g.n - t) = g.n + 1 from by omega, ← a1S_eq] at h
  exact h.trans (a1S_final g)


theorem rest_fields (XXL : Array (Array (List Int)) × Array (Array (List Int))) (AT : Array (Array AttLayer))
    (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) (L0v : List Int) :
    ((X6.restAfterL0 g XXL AT EP L0v).run a).1.X = XXL.1 ∧ ((X6.restAfterL0 g XXL AT EP L0v).run a).1.XL = XXL.2 ∧
      ((X6.restAfterL0 g XXL AT EP L0v).run a).1.AT = AT := by
  simp only [X6.restAfterL0, X6.run_bind, X6.run_pure]
  trivial

theorem tail_fields (XXL : Array (Array (List Int)) × Array (Array (List Int))) (AT : Array (Array AttLayer))
    (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) :
    ((X6.tail g XXL AT EP).run a).1.X = XXL.1 ∧ ((X6.tail g XXL AT EP).run a).1.XL = XXL.2 ∧
      ((X6.tail g XXL AT EP).run a).1.AT = AT := by
  rw [X6.tail_eq_ite, X6.run_bind]
  exact rest_fields g XXL AT EP _ _

theorem lay_fields : (encodeCfg g).layout.X = (X5.XXLS g).1 ∧ (encodeCfg g).layout.XL = (X5.XXLS g).2 ∧
    (encodeCfg g).layout.AT = X5.ATS g := by
  obtain ⟨XXL, AT, e0, EP, a1, a2, ae, aP, b1, b2, be, bp, _hsz, _hpl⟩ := X6.decomp g
  have hlay : (encodeCfg g).layout = ((X6.tail g XXL AT EP).run aP).1 := by
    rw [X6.encodeCfg_layout, X6.layoutM_eq]
    simp only [X6.run_bind]
    rw [b1, b2, be, bp]
  have hXXL : XXL = X5.XXLS g := (congrArg Prod.fst b1).symm
  have ha1 : a1 = X5.a1S g := (congrArg Prod.snd b1).symm
  rw [hXXL, ha1] at b2
  have hAT : AT = X5.ATS g := (congrArg Prod.fst b2).symm
  rw [hlay, ← hXXL, ← hAT]
  exact tail_fields g XXL AT EP aP

theorem X_get (t : Nat) (ht : t ≤ g.n) : (encodeCfg g).layout.X.getD t #[] = (bVal g t).1 := by
  rw [(lay_fields g).1, XXLS_eq]
  exact X5.rangeMapArr_getD (fun t => (bVal g t).1) #[] (g.n + 1) t (by omega)

theorem XL_get (t : Nat) (ht : t ≤ g.n) : (encodeCfg g).layout.XL.getD t #[] = (bVal g t).2 := by
  rw [(lay_fields g).2.1, XXLS_eq]
  exact X5.rangeMapArr_getD (fun t => (bVal g t).2) #[] (g.n + 1) t (by omega)

theorem good_final (t s : Nat) (ht : t ≤ g.n) (hs : s ∈ g.NK) :
    GoodB (encodeCfg g).alloc t s (bVal g t) := by
  have hb := bloop t g.NK rep64 (bSt g t) (bSt_inv g t) (X5.NK_nodup g) (fun s' hs' => by
    have := X5.NK_lt g s' hs'
    exact ⟨by simp [rep64]; exact this, by simp [rep64]; exact this⟩)
  have e : bVal g t = (bres t g.NK rep64 (bSt g t)).1 := by
    unfold bVal
    rw [boardAlloc_run]
  have e2 : bSt g (t + 1) = (bres t g.NK rep64 (bSt g t)).2 := by
    show ((boardAlloc g t).run (bSt g t)).2 = _
    rw [boardAlloc_run]
  rw [e]
  refine goodB_congr _ _ t s _ _ ?_ rfl rfl (hb.2.2.2.2.2 s hs)
  rw [← e2]
  exact bSt_final g t ht


def clM (t x : Nat) : AM (List (List Nat × Int)) :=
  (attClears g x).mapM fun ss => fresh (.sem (.clear t ss)) >>= fun c => pure (ss, c)

def lidOf (X : Array (List Int)) (cl : List (List Nat × Int)) : ALit → Int
  | .x s k => xv X s k
  | .clr ss => ((cl.find? (·.1 == ss)).map (·.2)).getD 0

def conjM (t : Nat) (X : Array (List Int)) (cl : List (List Nat × Int)) (conj : List ALit) :
    AM (List Int × Option Int) :=
  if conj.length = 1 then pure (conj.map (lidOf X cl), none)
  else fresh (.conj (conj.map (ALit.sem t))) >>= fun v => pure (conj.map (lidOf X cl), some v)

def entM (t x : Nat) (X : Array (List Int)) (cl : List (List Nat × Int)) : AM (List AttEntry) :=
  (attAlts g x).mapM fun p => fresh (.sem (.att t x p.1)) >>= fun a =>
    p.2.mapM (conjM t X cl) >>= fun cs => pure ({ s := p.1, a, conjs := cs } : AttEntry)

def clearsOf (X : Array (List Int)) (cl : List (List Nat × Int)) : List (Int × Int × Int) :=
  cl.map fun p => (p.2, lidOf X cl ((clearLit p.1 (p.1.length - 1)).getD (.x 0 0)), xv X (p.1.getD (p.1.length - 1) 0) EMP)

theorem attAlloc_eq (t x : Nat) (X : Array (List Int)) :
    attAlloc g t x X = clM g t x >>= fun cl => entM g t x X cl >>= fun en =>
      pure ({ clears := clearsOf X cl, entries := en } : AttLayer) := by
  rfl


def step2 (XXL : Array (Array (List Int)) × Array (Array (List Int))) (t : Nat) (acc : Array (Array AttLayer)) :
    AM (Array (Array AttLayer)) :=
  attAlloc g t 0 (XXL.1.getD t #[]) >>= fun l0 => attAlloc g t 1 (XXL.1.getD t #[]) >>= fun l1 =>
    pure (acc.push #[l0, l1])

theorem L2_fold (XXL : Array (Array (List Int)) × Array (Array (List Int))) :
    X6.L2 g XXL = (List.range (g.n + 1)).foldlM (fun acc t => step2 g XXL t acc) #[] := by
  rw [← forIn_yieldB]
  unfold X6.L2 step2
  simp only [bind_assoc, pure_bind]

def Xt (t : Nat) : Array (List Int) := (X5.XXLS g).1.getD t #[]

def aSt : Nat → Alloc
  | 0 => X5.a1S g
  | t + 1 => ((attAlloc g t 1 (Xt g t)).run ((attAlloc g t 0 (Xt g t)).run (aSt t)).2).2

def mSt (t : Nat) : Alloc := ((attAlloc g t 0 (Xt g t)).run (aSt g t)).2

def aVal (t : Nat) : Array AttLayer :=
  #[((attAlloc g t 0 (Xt g t)).run (aSt g t)).1, ((attAlloc g t 1 (Xt g t)).run (mSt g t)).1]

theorem fold2_run : ∀ (k : Nat),
    ((List.range k).foldlM (fun acc t => step2 g (X5.XXLS g) t acc) #[]).run (X5.a1S g) =
      (((List.range k).map (aVal g)).toArray, aSt g k)
  | 0 => rfl
  | k + 1 => by
    rw [X6.foldlM_range_succ, X6.run_bind, fold2_run k]
    unfold step2
    rw [X6.run_bind, X6.run_bind, X6.run_pure]
    show ((((List.range k).map (aVal g)).toArray.push (aVal g k)), aSt g (k + 1)) = _
    rw [X5.rangeMapArr_push (aVal g)]

theorem ATS_eq : X5.ATS g = ((List.range (g.n + 1)).map (aVal g)).toArray := by
  unfold X5.ATS
  rw [L2_fold, fold2_run]

theorem a2S_eq : X5.a2S g = aSt g (g.n + 1) := by
  unfold X5.a2S
  rw [L2_fold, fold2_run]

theorem aSt_inv : ∀ t, (aSt g t).roles.size = (aSt g t).nv
  | 0 => (X6.L1_ext g { nv := 0, roles := #[] } rfl).1
  | t + 1 => (attAlloc_ext g t 1 _ _ (attAlloc_ext g t 0 _ (aSt g t) (aSt_inv t)).1).1

theorem mSt_inv (t : Nat) : (mSt g t).roles.size = (mSt g t).nv :=
  (attAlloc_ext g t 0 _ (aSt g t) (aSt_inv g t)).1

theorem aSt_step (t : Nat) : (aSt g t).roles.toList <+: (aSt g (t + 1)).roles.toList :=
  (attAlloc_ext g t 0 _ (aSt g t) (aSt_inv g t)).2.trans (attAlloc_ext g t 1 _ (mSt g t) (mSt_inv g t)).2

theorem aSt_chain : ∀ (t k : Nat), (aSt g t).roles.toList <+: (aSt g (t + k)).roles.toList
  | t, 0 => by rw [Nat.add_zero]; exact List.prefix_refl _
  | t, k + 1 => by
    rw [show t + (k + 1) = (t + k) + 1 from by omega]
    exact (aSt_chain t k).trans (aSt_step g (t + k))

theorem a2S_final : (X5.a2S g).roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have h2 := X6.L2_ext g (X5.XXLS g) (X5.a1S g) (X6.L1_ext g { nv := 0, roles := #[] } rfl).1
  have h3 : (X5.epSt g 0).roles.toList <+: (X5.pSt g 0).roles.toList :=
    (epAlloc_ext g 0 (X5.epSt g 0) h2.1).2
  exact h3.trans (X5.pSt_final g 0 (Nat.zero_le _))

theorem aSt_final (t : Nat) (ht : t ≤ g.n) :
    (aSt g (t + 1)).roles.toList <+: (encodeCfg g).alloc.roles.toList := by
  have h := aSt_chain g (t + 1) (g.n - t)
  rw [show t + 1 + (g.n - t) = g.n + 1 from by omega, ← a2S_eq] at h
  exact h.trans (a2S_final g)

theorem att_spec (t x : Nat) (ht : t ≤ g.n) (hx : x < 2) :
    ∃ a : Alloc, a.roles.size = a.nv ∧
      attAtL g t x = ((attAlloc g t x ((encodeCfg g).layout.X.getD t #[])).run a).1 ∧
      ((attAlloc g t x ((encodeCfg g).layout.X.getD t #[])).run a).2.roles.toList <+:
        (encodeCfg g).alloc.roles.toList := by
  have hX : (encodeCfg g).layout.X.getD t #[] = Xt g t := by
    rw [(lay_fields g).1]; rfl
  have hA : attAtL g t x = (aVal g t).getD x default := by
    show ((encodeCfg g).layout.AT.getD t #[]).getD x default = _
    rw [(lay_fields g).2.2, ATS_eq, X5.rangeMapArr_getD (aVal g) #[] (g.n + 1) t (by omega)]
  rw [hX, hA]
  have hx' : x = 0 ∨ x = 1 := by omega
  rcases hx' with rfl | rfl
  · refine ⟨aSt g t, aSt_inv g t, rfl, ?_⟩
    exact (attAlloc_ext g t 1 _ (mSt g t) (mSt_inv g t)).2.trans (aSt_final g t ht)
  · exact ⟨mSt g t, mSt_inv g t, rfl, aSt_final g t ht⟩


theorem mapM_post {α β : Type} (F : Alloc) (Q : α → β → Prop) (f : α → AM β) :
    ∀ (l : List α) (a : Alloc), a.roles.size = a.nv →
    (∀ x ∈ l, ∀ a : Alloc, a.roles.size = a.nv →
      ((f x).run a).2.roles.size = ((f x).run a).2.nv ∧ a.roles.toList <+: ((f x).run a).2.roles.toList ∧
      (((f x).run a).2.roles.toList <+: F.roles.toList → Q x ((f x).run a).1)) →
    ((l.mapM f).run a).2.roles.size = ((l.mapM f).run a).2.nv ∧
      a.roles.toList <+: ((l.mapM f).run a).2.roles.toList ∧
      (((l.mapM f).run a).2.roles.toList <+: F.roles.toList → Fa2 (fun y x => Q x y) ((l.mapM f).run a).1 l)
  | [], a, ha, _ => ⟨ha, List.prefix_refl _, fun _ => trivial⟩
  | x :: l, a, ha, hf => by
    rw [List.mapM_cons, X6.run_bind, X6.run_bind, X6.run_pure]
    obtain ⟨h1, h2, h3⟩ := hf x List.mem_cons_self a ha
    obtain ⟨k1, k2, k3⟩ := mapM_post F Q f l ((f x).run a).2 h1 (fun y hy => hf y (List.mem_cons_of_mem _ hy))
    exact ⟨k1, h2.trans k2, fun hp => ⟨h3 (k2.trans hp), k3 hp⟩⟩

theorem fa2_imp {α β : Type} {R R' : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Fa2 R as bs → (∀ a b, a ∈ as → b ∈ bs → R a b → R' a b) → Fa2 R' as bs
  | [], [], _, _ => trivial
  | x :: as, y :: bs, h, hi => by
    have h1 : R x y ∧ Fa2 R as bs := h
    exact ⟨hi x y List.mem_cons_self List.mem_cons_self h1.1,
      fa2_imp h1.2 (fun a b ha hb hr => hi a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb) hr)⟩
  | [], _ :: _, h, _ => by simp [Fa2] at h
  | _ :: _, [], h, _ => by simp [Fa2] at h

theorem fa2_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Fa2 R as bs → ∀ {b : β}, b ∈ bs → ∃ a, a ∈ as ∧ R a b
  | [], [], _, _, hb => absurd hb List.not_mem_nil
  | x :: as, y :: ys, h, _, hb => by
      have h1 : R x y ∧ Fa2 R as ys := h
      rcases List.mem_cons.mp hb with rfl | hy
      · exact ⟨x, List.mem_cons_self, h1.1⟩
      · obtain ⟨a, ha, hr⟩ := fa2_mem_right h1.2 hy
        exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩
  | [], _ :: _, h, _, _ => by simp [Fa2] at h
  | _ :: _, [], h, _, _ => by simp [Fa2] at h

theorem fa2_map_eq {α β γ : Type} {R : α → β → Prop} (f : α → γ) (k : β → γ) (hR : ∀ a b, R a b → f a = k b) :
    ∀ {as : List α} {bs : List β}, Fa2 R as bs → as.map f = bs.map k
  | [], [], _ => rfl
  | x :: as, y :: bs, h => by
    have h1 : R x y ∧ Fa2 R as bs := h
    rw [List.map_cons, List.map_cons, hR x y h1.1, fa2_map_eq f k hR h1.2]
  | [], _ :: _, h => by simp [Fa2] at h
  | _ :: _, [], h => by simp [Fa2] at h

theorem fa2_map_self {α β : Type} (R : α → β → Prop) (f : β → α) :
    ∀ (bs : List β), (∀ b ∈ bs, R (f b) b) → Fa2 R (bs.map f) bs
  | [], _ => trivial
  | b :: bs, h => ⟨h b List.mem_cons_self, fa2_map_self R f bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))⟩

theorem fresh_pair_spec {γ : Type} (r : Role) (k : Int → γ) (a : Alloc) (ha : a.roles.size = a.nv) :
    ((fresh r >>= fun c => pure (k c) : AM γ).run a).2.roles.size =
        ((fresh r >>= fun c => pure (k c) : AM γ).run a).2.nv ∧
      a.roles.toList <+: ((fresh r >>= fun c => pure (k c) : AM γ).run a).2.roles.toList ∧
      ((fresh r >>= fun c => pure (k c) : AM γ).run a).1 = k ((fresh r).run a).1 ∧
      (((fresh r >>= fun c => pure (k c) : AM γ).run a).2.roles.toList <+: (encodeCfg g).alloc.roles.toList →
        HasRole (encodeCfg g) ((fresh r).run a).1 r) := by
  rw [X6.run_bind, X6.run_pure]
  obtain ⟨e1, e2⟩ := fresh_ext r a ha
  obtain ⟨f1, f2⟩ := fresh_role r a ha
  exact ⟨e1, e2, rfl, fun hp => hasRole_of_prefix g _ _ _ f1 hp f2⟩

theorem clM_spec (t x : Nat) (a : Alloc) (ha : a.roles.size = a.nv) :
    ((clM g t x).run a).2.roles.size = ((clM g t x).run a).2.nv ∧
      a.roles.toList <+: ((clM g t x).run a).2.roles.toList ∧
      (((clM g t x).run a).2.roles.toList <+: (encodeCfg g).alloc.roles.toList →
        Fa2 (fun y ss => y.1 = ss ∧ HasRole (encodeCfg g) y.2 (.sem (.clear t ss))) ((clM g t x).run a).1
          (attClears g x)) := by
  refine mapM_post (encodeCfg g).alloc (fun ss (y : List Nat × Int) => y.1 = ss ∧ HasRole (encodeCfg g) y.2 (.sem (.clear t ss)))
    _ (attClears g x) a ha ?_
  intro ss _ a' ha'
  obtain ⟨p1, p2, p3, p4⟩ := fresh_pair_spec g (.sem (.clear t ss)) (fun c => (ss, c)) a' ha'
  refine ⟨p1, p2, fun hp => ?_⟩
  rw [p3]
  exact ⟨rfl, p4 hp⟩

def QC (t : Nat) (lid : ALit → Int) (conj : List ALit) (c : List Int × Option Int) : Prop :=
  c.1 = conj.map lid ∧ (c.2 = none ↔ conj.length = 1) ∧
    ∀ v, c.2 = some v → HasRole (encodeCfg g) v (.conj (conj.map (ALit.sem t)))

theorem conjM_spec (t : Nat) (X : Array (List Int)) (cl : List (List Nat × Int)) (conj : List ALit)
    (a : Alloc) (ha : a.roles.size = a.nv) :
    ((conjM t X cl conj).run a).2.roles.size = ((conjM t X cl conj).run a).2.nv ∧
      a.roles.toList <+: ((conjM t X cl conj).run a).2.roles.toList ∧
      (((conjM t X cl conj).run a).2.roles.toList <+: (encodeCfg g).alloc.roles.toList →
        QC g t (lidOf X cl) conj ((conjM t X cl conj).run a).1) := by
  unfold conjM
  by_cases h1 : conj.length = 1
  · rw [ite_eq_left h1, X6.run_pure]
    exact ⟨ha, List.prefix_refl _, fun _ => ⟨rfl, ⟨fun _ => h1, fun _ => rfl⟩, fun v hv => by cases hv⟩⟩
  · rw [ite_eq_right h1]
    obtain ⟨p1, p2, p3, p4⟩ := fresh_pair_spec g (.conj (conj.map (ALit.sem t)))
      (fun v => (conj.map (lidOf X cl), some v)) a ha
    refine ⟨p1, p2, fun hp => ?_⟩
    rw [p3]
    show (conj.map (lidOf X cl) = conj.map (lidOf X cl)) ∧
      ((some ((fresh (.conj (conj.map (ALit.sem t)))).run a).1 = none) ↔ conj.length = 1) ∧
      ∀ v, some ((fresh (.conj (conj.map (ALit.sem t)))).run a).1 = some v →
        HasRole (encodeCfg g) v (.conj (conj.map (ALit.sem t)))
    refine ⟨rfl, ⟨fun hh => (by cases hh), fun hh => absurd hh h1⟩, fun v hv => ?_⟩
    rw [← Option.some.inj hv]
    exact p4 hp

def QE (t x : Nat) (lid : ALit → Int) (p : Nat × List (List ALit)) (en : AttEntry) : Prop :=
  en.s = p.1 ∧ HasRole (encodeCfg g) en.a (.sem (.att t x p.1)) ∧ Fa2 (fun c al => QC g t lid al c) en.conjs p.2

theorem entM_spec (t x : Nat) (X : Array (List Int)) (cl : List (List Nat × Int)) (a : Alloc)
    (ha : a.roles.size = a.nv) :
    ((entM g t x X cl).run a).2.roles.size = ((entM g t x X cl).run a).2.nv ∧
      a.roles.toList <+: ((entM g t x X cl).run a).2.roles.toList ∧
      (((entM g t x X cl).run a).2.roles.toList <+: (encodeCfg g).alloc.roles.toList →
        Fa2 (fun en p => QE g t x (lidOf X cl) p en) ((entM g t x X cl).run a).1 (attAlts g x)) := by
  refine mapM_post (encodeCfg g).alloc (QE g t x (lidOf X cl)) _ (attAlts g x) a ha ?_
  intro p _ a' ha'
  rw [X6.run_bind, X6.run_bind, X6.run_pure]
  obtain ⟨e1, e2⟩ := fresh_ext (.sem (.att t x p.1)) a' ha'
  obtain ⟨f1, f2⟩ := fresh_role (.sem (.att t x p.1)) a' ha'
  obtain ⟨k1, k2, k3⟩ := mapM_post (encodeCfg g).alloc (QC g t (lidOf X cl)) (conjM t X cl) p.2 _ e1
    (fun conj _ a'' ha'' => conjM_spec g t X cl conj a'' ha'')
  exact ⟨k1, e2.trans k2, fun hp => ⟨rfl, hasRole_of_prefix g _ _ _ f1 (k2.trans hp) f2, k3 hp⟩⟩


theorem ray_NK (x : Nat) (hx : x < 2) (d : Int × Int) (hd : d ∈ orth ++ diag) (s : Nat) (hs : s ∈ g.ray x d) :
    s ∈ g.NK := by
  obtain ⟨j, hj, hsj⟩ := List.mem_iff_getElem.mp hs
  have hsd : (g.ray x d).getD j 0 = s := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hsj]
  have hj' := hj
  rw [ray_eq_go] at hj'
  obtain ⟨hlt, _, _⟩ := go_getD d (g.K (1 - x)) 8 _ _ j hj'
  rw [← ray_eq_go, hsd] at hlt
  have hno : s ≠ g.K (1 - x) := go_ne_o d (g.K (1 - x)) 8 _ _ s (by rw [← ray_eq_go]; exact hs)
  have hnk : s ≠ g.K x := by
    intro he
    by_cases hK : g.K x < 64
    · obtain ⟨_, hf, hr⟩ := ray_getD g x d hd hK j hj
      rw [hsd, he] at hf hr
      have e1 : ((j : Int) + 1) * d.1 = 0 := by omega
      have e2 : ((j : Int) + 1) * d.2 = 0 := by omega
      have hj0 : (j : Int) + 1 ≠ 0 := by omega
      rcases mem_orth_diag_ne d hd with h | h
      · rcases Int.mul_eq_zero.mp e1 with h' | h'
        · exact hj0 h'
        · exact h h'
      · rcases Int.mul_eq_zero.mp e2 with h' | h'
        · exact hj0 h'
        · exact h h'
    · omega
  refine List.mem_filter.mpr ⟨List.mem_range.mpr hlt, ?_⟩
  have hx' : x = 0 ∨ x = 1 := by omega
  have hw : s ≠ g.kw := by
    rcases hx' with rfl | rfl
    · exact hnk
    · exact hno
  have hb : s ≠ g.kb := by
    rcases hx' with rfl | rfl
    · exact hno
    · exact hnk
  unfold Cfg.isK
  rw [beq_false_of_ne hw, beq_false_of_ne hb]
  rfl

theorem mem_attClears (x : Nat) (ss : List Nat) :
    ss ∈ attClears g x ↔ ∃ d ∈ orth ++ diag, ∃ j, j < (g.ray x d).length ∧ 2 ≤ j ∧ ss = (g.ray x d).take j := by
  unfold attClears
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨d, hd, hm⟩
    obtain ⟨j, hj, hjs⟩ := List.mem_map.mp hm
    obtain ⟨hj1, hj2⟩ := List.mem_filter.mp hj
    exact ⟨d, hd, j, List.mem_range.mp hj1, of_decide_eq_true hj2, hjs.symm⟩
  · rintro ⟨d, hd, j, hj, h2, rfl⟩
    exact ⟨d, hd, List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj, decide_eq_true h2⟩, rfl⟩⟩

theorem take_getD (l : List Nat) (j i : Nat) (h : i < j) : (l.take j).getD i 0 = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

def GoodL (x : Nat) : ALit → Prop
  | .x s k => s ∈ g.NK ∧ k < 11
  | .clr ss => ss ∈ attClears g x

theorem find_cl (cl : List (List Nat × Int)) (ss : List Nat) (p : List Nat × Int) (hp : p ∈ cl) (he : p.1 = ss) :
    ∃ q ∈ cl, cl.find? (·.1 == ss) = some q ∧ q.1 = ss := by
  cases hf : cl.find? (·.1 == ss) with
  | none =>
    have := List.find?_eq_none.mp hf p hp
    rw [he] at this
    exact absurd (beq_self_eq_true ss) this
  | some q =>
    refine ⟨q, List.mem_of_find?_eq_some hf, rfl, ?_⟩
    have h := List.find?_some (p := fun x : List Nat × Int => x.fst == ss) hf
    exact beq_iff_eq.mp h

theorem lid_role (t x : Nat) (ht : t ≤ g.n) (cl : List (List Nat × Int))
    (hcl : Fa2 (fun y ss => y.1 = ss ∧ HasRole (encodeCfg g) y.2 (.sem (.clear t ss))) cl (attClears g x))
    (al : ALit) (hal : GoodL g x al) :
    HasRole (encodeCfg g) (lidOf ((encodeCfg g).layout.X.getD t #[]) cl al) (.sem (al.sem t)) := by
  cases al with
  | x s k =>
    show HasRole (encodeCfg g) (xv ((encodeCfg g).layout.X.getD t #[]) s k) (.sem (.x t s k))
    rw [X_get g t ht]
    exact (good_final g t s ht hal.1).1 k hal.2
  | clr ss =>
    obtain ⟨p, hp, hpe, _⟩ := fa2_mem_right hcl hal
    obtain ⟨q, hq, hfq, hq1⟩ := find_cl cl ss p hp hpe
    obtain ⟨ss', _, hq1', hrole⟩ := fa2_mem_left hcl hq
    show HasRole (encodeCfg g) (((cl.find? (·.1 == ss)).map (·.2)).getD 0) (.sem (.clear t ss))
    rw [hfq]
    rw [← hq1, hq1']
    exact hrole


theorem attAlloc_run (t x : Nat) (X : Array (List Int)) (a : Alloc) :
    (attAlloc g t x X).run a =
      (({ clears := clearsOf X ((clM g t x).run a).1,
          entries := ((entM g t x X ((clM g t x).run a).1).run ((clM g t x).run a).2).1 } : AttLayer),
        ((entM g t x X ((clM g t x).run a).1).run ((clM g t x).run a).2).2) := by
  rw [attAlloc_eq, X6.run_bind, X6.run_bind, X6.run_pure]

theorem clearLit_good (x : Nat) (hx : x < 2) (d : Int × Int) (hd : d ∈ orth ++ diag) (j : Nat)
    (hj : j < (g.ray x d).length) : ∀ b ∈ (clearLit (g.ray x d) j).toList, GoodL g x b := by
  intro b hb
  unfold clearLit at hb
  by_cases h0 : j = 0
  · rw [ite_eq_left h0] at hb
    exact absurd hb List.not_mem_nil
  · rw [ite_eq_right h0] at hb
    by_cases h1 : j = 1
    · rw [ite_eq_left h1] at hb
      rw [List.mem_singleton.mp hb]
      exact ⟨ray_NK g x hx d hd _ (getD_mem _ _ _ (by omega)), by decide⟩
    · rw [ite_eq_right h1] at hb
      rw [List.mem_singleton.mp hb]
      exact (mem_attClears g x _).mpr ⟨d, hd, j, hj, by omega, rfl⟩

theorem conj_good (x : Nat) (hx : x < 2) (p : Nat × List (List ALit)) (hp : p ∈ attAlts g x) (al : List ALit)
    (hal : al ∈ p.2) : ∀ b ∈ al, GoodL g x b := by
  intro b hb
  rcases (mem_attAlts_iff g x hx p.1 al).mp ⟨p.2, hp, hal⟩ with ⟨hs, _, he⟩ | ⟨hs, _, he⟩ |
      ⟨d, hd, j, hj, hsj, pc, hpc, he⟩
  · rw [he, List.mem_singleton] at hb
    rw [hb]
    exact ⟨hs, by unfold N; omega⟩
  · rw [he, List.mem_singleton] at hb
    rw [hb]
    exact ⟨hs, by unfold P; omega⟩
  · rw [he, List.mem_append] at hb
    rcases hb with hb | hb
    · exact clearLit_good g x hx d hd j hj b hb
    · rw [List.mem_singleton] at hb
      rw [hb]
      refine ⟨by rw [hsj]; exact ray_NK g x hx d hd _ (getD_mem _ _ _ hj), ?_⟩
      have hpc' : pc ≤ 4 := by
        rw [List.mem_cons, List.mem_singleton] at hpc
        rcases hpc with h | h
        · rw [h]; decide
        · rw [h]; split <;> decide
      omega

theorem entries_of (t x : Nat) (ht : t ≤ g.n) (hx : x < 2) (a : Alloc) (ha : a.roles.size = a.nv)
    (hpre : ((attAlloc g t x ((encodeCfg g).layout.X.getD t #[])).run a).2.roles.toList <+:
      (encodeCfg g).alloc.roles.toList) :
    ((attAlloc g t x ((encodeCfg g).layout.X.getD t #[])).run a).1.entries.map (·.s) = (attAlts g x).map (·.1) ∧
      ∀ en ∈ ((attAlloc g t x ((encodeCfg g).layout.X.getD t #[])).run a).1.entries, ∃ cs, (en.s, cs) ∈ attAlts g x ∧
        HasRole (encodeCfg g) en.a (.sem (.att t x en.s)) ∧
        Fa2 (fun (c : List Int × Option Int) (al : List ALit) =>
            Fa2 (fun l a => HasRole (encodeCfg g) l (.sem (a.sem t))) c.1 al ∧
            (c.2 = none ↔ al.length = 1) ∧
            ∀ v, c.2 = some v → HasRole (encodeCfg g) v (.conj (al.map (ALit.sem t))))
          en.conjs cs := by
  rw [attAlloc_run] at hpre ⊢
  obtain ⟨c1, c2, c3⟩ := clM_spec g t x a ha
  obtain ⟨e1, e2, e3⟩ := entM_spec g t x ((encodeCfg g).layout.X.getD t #[]) ((clM g t x).run a).1 _ c1
  have hcl := c3 (e2.trans hpre)
  have hE := e3 hpre
  refine ⟨fa2_map_eq (·.s) (·.1) (fun _ _ h => h.1) hE, ?_⟩
  intro en hen
  obtain ⟨p, hp, hq⟩ := fa2_mem_left hE hen
  refine ⟨p.2, by rw [hq.1]; exact hp, by rw [hq.1]; exact hq.2.1, fa2_imp hq.2.2 ?_⟩
  intro c al _ hal hQC
  obtain ⟨q1, q2, q3⟩ := hQC
  refine ⟨?_, q2, q3⟩
  rw [q1]
  exact fa2_map_self _ _ al (fun b hb => lid_role g t x ht _ hcl b (conj_good g x hx p hp al hal b hb))

theorem clearLit_take (l : List Nat) (i j : Nat) (h : i < j) : clearLit (l.take j) i = clearLit l i := by
  unfold clearLit
  by_cases h0 : i = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases h1 : i = 1
    · rw [ite_eq_left h1, ite_eq_left h1, take_getD _ _ _ (by omega)]
    · rw [ite_eq_right h1, ite_eq_right h1, List.take_take, Nat.min_eq_left (by omega)]

theorem clearLit_some (l : List Nat) (i : Nat) (h : i ≠ 0) : ∃ b, clearLit l i = some b := by
  unfold clearLit
  rw [ite_eq_right h]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem clears_of (t x : Nat) (ht : t ≤ g.n) (hx : x < 2) (a : Alloc) (ha : a.roles.size = a.nv)
    (hpre : ((attAlloc g t x ((encodeCfg g).layout.X.getD t #[])).run a).2.roles.toList <+:
      (encodeCfg g).alloc.roles.toList) :
    ∀ tr ∈ ((attAlloc g t x ((encodeCfg g).layout.X.getD t #[])).run a).1.clears, ∃ ss ∈ attClears g x,
      HasRole (encodeCfg g) tr.1 (.sem (.clear t ss)) ∧
      HasRole (encodeCfg g) tr.2.1 (.sem (((clearLit ss (ss.length - 1)).getD (.x 0 0)).sem t)) ∧
      HasRole (encodeCfg g) tr.2.2 (.sem (.x t (ss.getD (ss.length - 1) 0) EMP)) := by
  rw [attAlloc_run] at hpre ⊢
  obtain ⟨c1, c2, c3⟩ := clM_spec g t x a ha
  obtain ⟨e1, e2, e3⟩ := entM_spec g t x ((encodeCfg g).layout.X.getD t #[]) ((clM g t x).run a).1 _ c1
  have hcl := c3 (e2.trans hpre)
  intro tr htr
  obtain ⟨p, hp, hpt⟩ := List.mem_map.mp htr
  obtain ⟨ss, hss, hp1, hrole⟩ := fa2_mem_left hcl hp
  rw [← hpt]
  refine ⟨ss, hss, hrole, ?_, ?_⟩
  · obtain ⟨d, hd, j, hj, h2, hsj⟩ := (mem_attClears g x ss).mp hss
    have hlen : ss.length = j := by rw [hsj, List.length_take]; omega
    obtain ⟨b, hb⟩ := clearLit_some ss (ss.length - 1) (by omega)
    show HasRole (encodeCfg g) (lidOf _ _ ((clearLit p.1 (p.1.length - 1)).getD (.x 0 0))) _
    rw [hp1, hb]
    have hb' : b ∈ (clearLit (g.ray x d) (j - 1)).toList := by
      rw [← clearLit_take _ _ j (by omega), ← hsj, ← hlen, hb]
      exact List.mem_singleton_self b
    exact lid_role g t x ht _ hcl b (clearLit_good g x hx d hd (j - 1) (by omega) b hb')
  · obtain ⟨d, hd, j, hj, h2, hsj⟩ := (mem_attClears g x ss).mp hss
    have hlen : ss.length = j := by rw [hsj, List.length_take]; omega
    show HasRole (encodeCfg g) (xv _ (p.1.getD (p.1.length - 1) 0) EMP) _
    rw [hp1, X_get g t ht]
    have hm : ss.getD (ss.length - 1) 0 ∈ g.NK := by
      rw [hlen, hsj, take_getD _ _ _ (by omega)]
      exact ray_NK g x hx d hd _ (getD_mem _ _ _ (by omega))
    exact (good_final g t _ ht hm).1 EMP (by decide)

end X4


theorem roles_X (t s k : Nat) (ht : t ≤ g.n) (hs : s ∈ g.NK) (hk : k < 11) :
    HasRole (encodeCfg g) (xv ((encodeCfg g).layout.X.getD t #[]) s k) (.sem (.x t s k)) := by
  rw [X4.X_get g t ht]
  exact (X4.good_final g t s ht hs).1 k hk

theorem roles_XL (t s : Nat) (ht : t ≤ g.n) (hs : s ∈ g.NK) :
    (((encodeCfg g).layout.XL.getD t #[]).getD s []).length = 10 ∧
      ∀ i, i < 10 → HasRole (encodeCfg g) ((((encodeCfg g).layout.XL.getD t #[]).getD s []).getD i 0)
        (.ladder ((List.range 11).map (Sem.x t s)) i) := by
  rw [X4.XL_get g t ht]
  exact ⟨(X4.good_final g t s ht hs).2.1, (X4.good_final g t s ht hs).2.2⟩

theorem roles_clears (t x : Nat) (ht : t ≤ g.n) (hx : x < 2) :
    ∀ tr ∈ (attAtL g t x).clears, ∃ ss ∈ attClears g x,
      HasRole (encodeCfg g) tr.1 (.sem (.clear t ss)) ∧
      HasRole (encodeCfg g) tr.2.1 (.sem (((clearLit ss (ss.length - 1)).getD (.x 0 0)).sem t)) ∧
      HasRole (encodeCfg g) tr.2.2 (.sem (.x t (ss.getD (ss.length - 1) 0) EMP)) := by
  obtain ⟨a, ha, hA, hpre⟩ := X4.att_spec g t x ht hx
  rw [hA]
  exact X4.clears_of g t x ht hx a ha hpre

theorem roles_entries (t x : Nat) (ht : t ≤ g.n) (hx : x < 2) :
    (attAtL g t x).entries.map (·.s) = (attAlts g x).map (·.1) ∧
      ∀ en ∈ (attAtL g t x).entries, ∃ cs, (en.s, cs) ∈ attAlts g x ∧
        HasRole (encodeCfg g) en.a (.sem (.att t x en.s)) ∧
        Fa2 (fun (c : List Int × Option Int) (al : List ALit) =>
            Fa2 (fun l a => HasRole (encodeCfg g) l (.sem (a.sem t))) c.1 al ∧
            (c.2 = none ↔ al.length = 1) ∧
            ∀ v, c.2 = some v → HasRole (encodeCfg g) v (.conj (al.map (ALit.sem t))))
          en.conjs cs := by
  obtain ⟨a, ha, hA, hpre⟩ := X4.att_spec g t x ht hx
  rw [hA]
  exact X4.entries_of g t x ht hx a ha hpre

theorem roles_eps (t : Nat) (ht : t ≤ g.n) :
    ((encodeCfg g).layout.EPS.getD t []).map (·.1) = epSquares g t ∧
      ∀ sv ∈ (encodeCfg g).layout.EPS.getD t [], HasRole (encodeCfg g) sv.2 (.sem (.eps t sv.1)) := X5.roles_eps5 g t ht

theorem roles_FRTO (t s : Nat) (ht : t < g.n) (hs : s ∈ g.NK) :
    HasRole (encodeCfg g) ((plyAt g t).FR.getD s 0) (.sem (.fr t s)) ∧
      HasRole (encodeCfg g) ((plyAt g t).TO.getD s 0) (.sem (.to t s)) := X5.roles_FRTO5 g t s ht hs

theorem roles_MPRT (t : Nat) (ht : t < g.n) :
    (plyAt g t).MP.length = 5 ∧ (plyAt g t).RT.length = 5 ∧
      ∀ p, p < 5 → HasRole (encodeCfg g) ((plyAt g t).MP.getD p 0) (.sem (.mp t p)) ∧
        HasRole (encodeCfg g) ((plyAt g t).RT.getD p 0) (.sem (.rt t p)) := X5.roles_MPRT5 g t ht

theorem roles_CAPPROMO (t : Nat) (ht : t < g.n) :
    HasRole (encodeCfg g) (plyAt g t).CAP (.sem (.cap t)) ∧ HasRole (encodeCfg g) (plyAt g t).PROMO (.sem (.promo t)) := X5.roles_CAPPROMO5 g t ht

theorem roles_FRTOL (t : Nat) (ht : t < g.n) :
    (plyAt g t).FRL.length = g.NK.length - 1 ∧ (plyAt g t).TOL.length = g.NK.length - 1 ∧
      ∀ i, i < g.NK.length - 1 →
        HasRole (encodeCfg g) ((plyAt g t).FRL.getD i 0) (.ladder (g.NK.map (Sem.fr t)) i) ∧
        HasRole (encodeCfg g) ((plyAt g t).TOL.getD i 0) (.ladder (g.NK.map (Sem.to t)) i) := X5.roles_FRTOL5 g t ht

theorem roles_EPR (t : Nat) (ht : t < g.n) :
    (plyAt g t).EPR.map (·.1) = (eprSquares g t ((encodeCfg g).layout.EPS.getD t [])).map (·.1) ∧
      ∀ rv ∈ (plyAt g t).EPR, HasRole (encodeCfg g) rv.2 (.sem (.epr t rv.1)) := X5.roles_EPR5 g t ht

theorem roles_CH (t : Nat) (ht : t < g.n) :
    (plyAt g t).CH.length = g.NK.length ∧
      ∀ i, i < g.NK.length → HasRole (encodeCfg g) ((plyAt g t).CH.getD i 0) (.sem (.ch t (g.NK.getD i 0))) := X5.roles_CH5 g t ht

theorem roles_L0 (h1 : 1 ≤ g.n) :
    let A := (attAtL g 0 0).A
    (8 < A.length → (encodeCfg g).layout.L0.length = A.length - 1) ∧
      ∀ i, i < (encodeCfg g).layout.L0.length → HasRole (encodeCfg g) ((encodeCfg g).layout.L0.getD i 0) (.ladder (A.map fun sa => Sem.att 0 0 sa.1) i) := X6.rolesX6_L0 g h1

theorem roles_LS (t : Nat) (ht : t + 1 ≤ g.n - 1) :
    let e := 1 - g.col t
    let A := (attAtL g (t + 1) e).A
    (8 < A.length → ((encodeCfg g).layout.LS.getD t []).length = A.length - 1) ∧
      ∀ i, i < ((encodeCfg g).layout.LS.getD t []).length →
        HasRole (encodeCfg g) (((encodeCfg g).layout.LS.getD t []).getD i 0) (.ladder (A.map fun sa => Sem.att (t + 1) e sa.1) i) := X6.rolesX6_LS g t ht

theorem roles_S (h1 : 1 ≤ g.n) (hm : g.m ≠ 0) :
    (encodeCfg g).layout.S.size = g.n ∧ ∀ i, i < g.n → ((encodeCfg g).layout.S.getD i []).length = g.m + 1 ∧
      ∀ j, j < g.m + 1 → HasRole (encodeCfg g) (((encodeCfg g).layout.S.getD i []).getD j 0) (.count ((List.range g.n).map Sem.cap) i j) := X6.rolesX6_S g h1 hm

theorem caps_layout (t : Nat) (ht : t < g.n) : ((encodeCfg g).layout.PL.toList.map (·.CAP)).getD t 0 = (plyAt g t).CAP := X6.caps_layout' g t ht

theorem PL_size : (encodeCfg g).layout.PL.size = g.n := X6.PL_size_PL g

end Roles

section Cores

variable {w b : Sq} {n m : Nat} {p : Pos} {ms : List Move}

def cfgOf (w b : Sq) (n m : Nat) : Cfg := { kw := w.val, kb := b.val, n, m }

theorem encode_cfg (w b : Sq) (n m : Nat) : encode w b n m = encodeCfg (cfgOf w b n m) := rfl

theorem take_succ_getD' {α : Type} (d : α) : ∀ (l : List α) (i : Nat), i < l.length →
    l.take (i + 1) = l.take i ++ [l.getD i d]
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => by
      show _ :: l.take (i + 1) = _ :: (l.take i ++ [l.getD i d])
      rw [take_succ_getD' d l i (by simpa using h)]
  | [], _, h => by simp at h

theorem run_step (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n) :
    (runOf p ms).mv t ∈ legalMoves ((runOf p ms).pos t) ∧ givesCheck ((runOf p ms).pos t) ((runOf p ms).mv t) = true ∧
      isKingMove ((runOf p ms).pos t) ((runOf p ms).mv t) = false ∧
      (runOf p ms).pos (t + 1) = play ((runOf p ms).pos t) ((runOf p ms).mv t) := by
  obtain ⟨hc0, hturn, hkw, hkb, hkf, hlen, hcaps⟩ := h
  have htl : t < ms.length := by omega
  have htake : ms.take (t + 1) = ms.take t ++ [(runOf p ms).mv t] := take_succ_getD' default ms t htl
  have hsplit : KFChain (after p (ms.take t)) [(runOf p ms).mv t] :=
    ((kf_append p (ms.take t) [(runOf p ms).mv t]).mp (by rw [← htake]; exact (kf_take p ms (t + 1) hkf).1)).2
  obtain ⟨hleg, hgc, hkm, -⟩ := hsplit
  refine ⟨hleg, hgc, hkm, ?_⟩
  show after p (ms.take (t + 1)) = play (after p (ms.take t)) ((runOf p ms).mv t)
  rw [htake, after_append]
  rfl

theorem run_c0 (h : ChainAt w b n m p ms) (t : Nat) (ht : t ≤ n) : C0 ((runOf p ms).pos t) := by
  obtain ⟨hc0, hturn, hkw, hkb, hkf, hlen, hcaps⟩ := h
  exact c0_after_kf p (ms.take t) hc0 (kf_take p ms t hkf).1

theorem run_turn (h : ChainAt w b n m p ms) (t : Nat) (ht : t ≤ n) :
    ((runOf p ms).pos t).turn = colorOf (t % 2) := by
  have hcopy := h
  obtain ⟨hc0, hturn, hkw, hkb, hkf, hlen, hcaps⟩ := hcopy
  have key : ∀ t, t ≤ n → ((runOf p ms).pos t).turn = colorOf (t % 2) := by
    intro t
    induction t with
    | zero =>
        intro _
        show p.turn = colorOf (0 % 2)
        rw [Nat.zero_mod, hturn]
        decide
    | succ t ih =>
        intro ht
        have hstep := (run_step h t (by omega)).2.2.2
        have hih := ih (by omega)
        rw [hstep, play_turn, hih]
        rcases (by omega : t % 2 = 0 ∨ t % 2 = 1) with h0 | h1
        · rw [h0, show (t + 1) % 2 = 1 by omega]; decide
        · rw [h1, show (t + 1) % 2 = 0 by omega]; decide
  exact key t ht

theorem run_kings (h : ChainAt w b n m p ms) (t : Nat) (ht : t ≤ n) :
    kingAt ((runOf p ms).pos t) .white w ∧ kingAt ((runOf p ms).pos t) .black b ∧
      ∀ s c, ((runOf p ms).pos t).board s = some ⟨c, .king⟩ → s = w ∨ s = b := by
  have hcopy := h
  obtain ⟨hc0, hturn, hkw, hkb, hkf, hlen, hcaps⟩ := hcopy
  have key : ∀ t, t ≤ n → kingAt ((runOf p ms).pos t) .white w ∧ kingAt ((runOf p ms).pos t) .black b ∧
      ∀ s c, ((runOf p ms).pos t).board s = some ⟨c, .king⟩ → s = w ∨ s = b := by
    intro t
    induction t with
    | zero =>
        intro _
        refine ⟨hkw, hkb, ?_⟩
        intro s c hs
        obtain ⟨w', hwk⟩ := hc0.wk
        obtain ⟨b', hbk⟩ := hc0.bk
        have hww : w = w' := (hwk w).mp hkw
        have hbb : b = b' := (hbk b).mp hkb
        cases c with
        | white => exact Or.inl (((hwk s).mp hs).trans hww.symm)
        | black => exact Or.inr (((hbk s).mp hs).trans hbb.symm)
    | succ t ih =>
        intro ht
        obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step h t (by omega)
        have hsaf := (run_c0 h t (by omega)).safe
        have hiff := kingAt_play_nonking ((runOf p ms).pos t) ((runOf p ms).mv t) hleg hkm hsaf
        obtain ⟨ihw, ihb, ihu⟩ := ih (by omega)
        refine ⟨?_, ?_, ?_⟩
        · rw [hstep]; exact (hiff .white w).mpr ihw
        · rw [hstep]; exact (hiff .black b).mpr ihb
        · intro s c hsc
          have h1 : kingAt (play ((runOf p ms).pos t) ((runOf p ms).mv t)) c s := by
            rw [← hstep]; exact hsc
          exact ihu s c ((hiff c s).mp h1)
  exact key t ht

theorem core_code (h : ChainAt w b n m p ms) (t : Nat) (ht : t ≤ n) (s : Nat) (hs : s ∈ (cfgOf w b n m).NK) :
    code (((runOf p ms).pos t).board (toSq s)) < 11 := by
  obtain ⟨hsr, hsk⟩ := List.mem_filter.mp hs
  have hs64 : s < 64 := List.mem_range.mp hsr
  have hne : s ≠ w.val ∧ s ≠ b.val := by
    simp [cfgOf, Cfg.isK] at hsk
    exact hsk
  have hk3 := (run_kings h t ht).2.2
  cases hb : ((runOf p ms).pos t).board (toSq s) with
  | none => decide
  | some q =>
      obtain ⟨c, k⟩ := q
      cases k with
      | king =>
          rcases hk3 (toSq s) c hb with h1 | h1
          · have hv : s = w.val := by
              have e1 : (toSq s).val = s := Nat.mod_eq_of_lt hs64
              rw [h1] at e1
              exact e1.symm
            exact absurd hv hne.1
          · have hv : s = b.val := by
              have e1 : (toSq s).val = s := Nat.mod_eq_of_lt hs64
              rw [h1] at e1
              exact e1.symm
            exact absurd hv hne.2
      | pawn => cases c <;> decide
      | knight => cases c <;> decide
      | bishop => cases c <;> decide
      | rook => cases c <;> decide
      | queen => cases c <;> decide

theorem core_src_dst (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n) :
    ((runOf p ms).mv t).src.val ∈ (cfgOf w b n m).NK ∧ ((runOf p ms).mv t).dst.val ∈ (cfgOf w b n m).NK := by
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step h t ht
  obtain ⟨q, hq, hqcol, -⟩ := legal_nonking_mem _ _ hleg hkm
  have hkq : q.kind ≠ .king := by
    have h1 : (q.kind == .king) = false := by simpa [isKingMove, hq] using hkm
    intro e
    rw [e] at h1
    simp at h1
  obtain ⟨hkw, hkb, -⟩ := run_kings h t (Nat.le_of_lt ht)
  have hsafe := (run_c0 h t (Nat.le_of_lt ht)).safe
  have hnk := legal_not_capture_king _ _ hleg hsafe
  have hsrcw : ((runOf p ms).mv t).src ≠ w := by
    intro e
    have e1 : ((runOf p ms).pos t).board w = some ⟨.white, .king⟩ := hkw
    rw [← e] at e1
    rw [hq] at e1
    injection e1 with e2
    exact hkq (by rw [e2])
  have hsrcb : ((runOf p ms).mv t).src ≠ b := by
    intro e
    have e1 : ((runOf p ms).pos t).board b = some ⟨.black, .king⟩ := hkb
    rw [← e] at e1
    rw [hq] at e1
    injection e1 with e2
    exact hkq (by rw [e2])
  have hdstw : ((runOf p ms).mv t).dst ≠ w := fun e => hnk .white (by rw [e]; exact hkw)
  have hdstb : ((runOf p ms).mv t).dst ≠ b := fun e => hnk .black (by rw [e]; exact hkb)
  have hsrcw' : ((runOf p ms).mv t).src.val ≠ w.val := Fin.val_ne_of_ne hsrcw
  have hsrcb' : ((runOf p ms).mv t).src.val ≠ b.val := Fin.val_ne_of_ne hsrcb
  have hdstw' : ((runOf p ms).mv t).dst.val ≠ w.val := Fin.val_ne_of_ne hdstw
  have hdstb' : ((runOf p ms).mv t).dst.val ≠ b.val := Fin.val_ne_of_ne hdstb
  constructor
  · exact List.mem_filter.mpr ⟨List.mem_range.mpr ((runOf p ms).mv t).src.isLt, by
      simp [cfgOf, Cfg.isK, hsrcw', hsrcb']⟩
  · exact List.mem_filter.mpr ⟨List.mem_range.mpr ((runOf p ms).mv t).dst.isLt, by
      simp [cfgOf, Cfg.isK, hdstw', hdstb']⟩

theorem color_parity (u : Nat) (hu : u < 2) :
    (u = 0 ∧ colorOf u = .white ∧ pdir u = 1 ∧ (colorOf u).fwd = 1 ∧ (colorOf u).pawnHome = 1) ∨
    (u = 1 ∧ colorOf u = .black ∧ pdir u = -1 ∧ (colorOf u).fwd = -1 ∧ (colorOf u).pawnHome = 6) := by
  rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
  · exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem isK_false_of_noking (pt : Pos) (zb : Nat)
    (hkw : kingAt pt .white w) (hkb : kingAt pt .black b)
    (hk : ∀ c, pt.board (toSq zb) ≠ some ⟨c, .king⟩) :
    (cfgOf w b n m).isK zb = false := by
  have hzw : zb ≠ w.val := fun e => hk .white (by rw [e, toSq_val]; exact hkw)
  have hzb : zb ≠ b.val := fun e => hk .black (by rw [e, toSq_val]; exact hkb)
  show (zb == w.val || zb == b.val) = false
  rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
  exact ⟨hzw, hzb⟩

theorem kdist_eq_zero {a b : Sq} (h : kdist a b = 0) : a = b := by
  simp only [kdist] at h
  have h1 : (fx a - fx b).natAbs = 0 := by omega
  have h2 : (ry a - ry b).natAbs = 0 := by omega
  exact sq_eq_of_coords a b (by omega) (by omega)

theorem inSeg_false_of_kdist_one (a b z : Sq) (h : kdist a b = 1) : inSeg a b z = false := by
  apply Bool.eq_false_iff.mpr
  intro hz
  simp only [inSeg, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hz
  obtain ⟨⟨⟨-, hza⟩, hzb⟩, hkd⟩ := hz
  rw [h] at hkd
  rcases (by omega : kdist a z = 0 ∨ kdist z b = 0) with h0 | h0
  · exact hza (kdist_eq_zero h0).symm
  · exact hzb (kdist_eq_zero h0)

theorem between_eq (a b : Nat) :
    between a b = (if fl b - fl a = 0 ∧ rk b - rk a = 0 then none
      else if fl b - fl a ≠ 0 ∧ rk b - rk a ≠ 0 ∧ (fl b - fl a).natAbs ≠ (rk b - rk a).natAbs then none
      else some ((List.range (max (fl b - fl a).natAbs (rk b - rk a).natAbs - 1)).map fun i : Nat =>
        sqOf (fl a + (fl b - fl a).sign * ((i : Int) + 1)) (rk a + (rk b - rk a).sign * ((i : Int) + 1)))) := rfl

theorem between_some_of_aligned (a b : Sq) (hal : aligned a b = true) :
    ∃ l, between a.val b.val = some l := by
  simp only [aligned, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, Bool.or_eq_true, or_assoc] at hal
  obtain ⟨hne, hor⟩ := hal
  have c1 : ¬ (fl b.val - fl a.val = 0 ∧ rk b.val - rk a.val = 0) := by
    rintro ⟨h1, h2⟩
    have h1' : fx b = fl b.val := rfl
    have h2' : fx a = fl a.val := rfl
    have h3' : ry b = rk b.val := rfl
    have h4' : ry a = rk a.val := rfl
    have e1 : fx a = fx b := by omega
    have e2 : ry a = ry b := by omega
    exact hne (sq_eq_of_coords a b e1 e2)
  have c2 : ¬ (fl b.val - fl a.val ≠ 0 ∧ rk b.val - rk a.val ≠ 0 ∧
      (fl b.val - fl a.val).natAbs ≠ (rk b.val - rk a.val).natAbs) := by
    rintro ⟨h1, h2, h3⟩
    rcases hor with h | h | h
    · have h1' : fx b = fl b.val := rfl
      have h2' : fx a = fl a.val := rfl
      exact h1 (by omega)
    · have h3' : ry b = rk b.val := rfl
      have h4' : ry a = rk a.val := rfl
      exact h2 (by omega)
    · have h1' : fx b = fl b.val := rfl
      have h2' : fx a = fl a.val := rfl
      have h3' : ry b = rk b.val := rfl
      have h4' : ry a = rk a.val := rfl
      exact h3 (by omega)
  rw [between_eq, if_neg c1, if_neg c2]
  exact ⟨_, rfl⟩

theorem allowed_eq (g : Cfg) (c f t : Nat) :
    g.allowed c f t =
      [(P, ((fl t - fl f == 0 && rk t - rk f == pdir c) ||
          (fl t - fl f == 0 && rk t - rk f == 2 * pdir c && rk f == (if c = 0 then (1 : Int) else 6) &&
            !g.isK (sqOf (fl f) (rk f + pdir c))) ||
          ((fl t - fl f).natAbs == 1 && rk t - rk f == pdir c))),
        (N, (((fl t - fl f).natAbs == 1 && (rk t - rk f).natAbs == 2) ||
          ((fl t - fl f).natAbs == 2 && (rk t - rk f).natAbs == 1))),
        (B, ((match between f t with | some l => !l.any g.isK | none => false) &&
          !(fl t - fl f == 0 || rk t - rk f == 0))),
        (R, ((match between f t with | some l => !l.any g.isK | none => false) &&
          (fl t - fl f == 0 || rk t - rk f == 0))),
        (Q, (match between f t with | some l => !l.any g.isK | none => false))].filterMap
        fun (p, b) => if b then some p else none := rfl

theorem epSquares_eq (g : Cfg) (t : Nat) :
    epSquares g t = g.NK.filter fun s =>
      rk s == (if g.col t = 0 then (5 : Int) else 2) && !g.isK (sqOf (fl s) (rk s - pdir (g.col t))) &&
        !g.isK (sqOf (fl s) (rk s + pdir (g.col t))) := rfl

theorem eprSquares_eq (g : Cfg) (t : Nat) (E : List (Nat × Int)) :
    eprSquares g t E = g.NK.filterMap fun r =>
      if rk r != (if g.col t = 0 then (4 : Int) else 3) then none
      else if (look E (sqOf (fl r) (rk r + pdir (g.col t)))).isNone then none
      else if ([-1, 1].filterMap fun df =>
          if onb (fl r + df) (rk r) && !g.isK (sqOf (fl r + df) (rk r)) then
            some (sqOf (fl r + df) (rk r)) else none).isEmpty then none
        else some (r, sqOf (fl r) (rk r + pdir (g.col t)),
          [-1, 1].filterMap fun df =>
            if onb (fl r + df) (rk r) && !g.isK (sqOf (fl r + df) (rk r)) then
              some (sqOf (fl r + df) (rk r)) else none) := rfl

theorem epVictim_eq (p : Pos) (m : Move) :
    epVictim p m = (if (p.board m.src).any (·.kind == .pawn) && m.src.file != m.dst.file &&
      empty p.board m.dst then some (sq m.dst.file m.src.rank) else none) := rfl

theorem toSq_sqOf_eq (x : Sq) (F R : Int) (honb : onb F R = true) (hf : fx x = F) (hr : ry x = R) :
    toSq (sqOf F R) = x := by
  obtain ⟨h64, hfl, hrk⟩ := onb_sqOf F R honb
  exact sq_eq_of_coords _ _ (by rw [fx_toSq _ h64, hfl, hf]) (by rw [ry_toSq _ h64, hrk, hr])

theorem inSeg_intro (a b z : Sq) (hne : (a != b) = true)
    (hor : (fx a == fx b || ry a == ry b || (fx a - fx b).natAbs == (ry a - ry b).natAbs) = true)
    (hcol : ((fx z - fx a) * (ry b - ry a) == (ry z - ry a) * (fx b - fx a)) = true)
    (hza : (z != a) = true) (hzb : (z != b) = true)
    (hkd : (kdist a z + kdist z b == kdist a b) = true) : inSeg a b z = true :=
  Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr
    ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨hne, hor⟩, hcol⟩, hza⟩, hzb⟩, hkd⟩

theorem sl_any_false (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n)
    (hclear : ∀ z, inSeg ((runOf p ms).mv t).src ((runOf p ms).mv t).dst z = true →
      ((runOf p ms).pos t).board z = none)
    (l : List Nat) (hbt : between ((runOf p ms).mv t).src.val ((runOf p ms).mv t).dst.val = some l) :
    l.any (cfgOf w b n m).isK = false := by
  obtain ⟨hkw, hkb, -⟩ := run_kings h t (Nat.le_of_lt ht)
  rw [List.any_eq_false]
  intro z hz hzk
  have hzbtw : z ∈ btw ((runOf p ms).mv t).src.val ((runOf p ms).mv t).dst.val := by
    rw [btw, hbt]
    exact hz
  obtain ⟨hz64, hseg⟩ :=
    (mem_btw_iff_nat ((runOf p ms).mv t).src ((runOf p ms).mv t).dst z).mp hzbtw
  have hbn := hclear (toSq z) hseg
  have hnok : ∀ cc, ((runOf p ms).pos t).board (toSq z) ≠ some ⟨cc, .king⟩ := fun cc hh => by
    rw [hbn] at hh; cases hh
  have hc : (cfgOf w b n m).isK z = false := isK_false_of_noking _ _ hkw hkb hnok
  exact absurd hzk (by rw [hc]; decide)

theorem core_allowed (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n) :
    ∃ q, ((runOf p ms).pos t).board ((runOf p ms).mv t).src = some q ∧
      ((cfgOf w b n m).allowed (t % 2) ((runOf p ms).mv t).src.val ((runOf p ms).mv t).dst.val).contains
        (kindIdx q.kind) = true := by
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step h t ht
  obtain ⟨q, hq, hqcol, hmem⟩ := legal_nonking_mem _ _ hleg hkm
  have lfs : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
  have lfd : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl
  have lrs : rk ((runOf p ms).mv t).src.val = ry ((runOf p ms).mv t).src := rfl
  have lrd : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
  have hpf2 : pdir (t % 2) = (colorOf (t % 2)).fwd := by
    rcases color_parity (t % 2) (Nat.mod_lt _ (by decide)) with ⟨-, hcol, hpd, hfw, -⟩ |
      ⟨-, hcol, hpd, hfw, -⟩ <;> rw [hpd, hfw]
  obtain ⟨c, k⟩ := q
  refine ⟨⟨c, k⟩, hq, ?_⟩
  cases k with
  | pawn =>
      obtain ⟨-, hdisj, -⟩ := pawnMoves_cases ((runOf p ms).pos t) ((runOf p ms).mv t).src
        c ((runOf p ms).mv t) hmem
      have hcc2 : c = colorOf (t % 2) := hqcol.trans (run_turn h t (Nat.le_of_lt ht))
      subst hcc2
      rcases hdisj with h1 | h2 | h3
      · obtain ⟨hfx1, hry1, -⟩ := h1
        have e1 : (fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0) = true :=
          beq_iff_eq.mpr (by omega)
        have e2 : (rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val ==
            pdir (t % 2)) = true := beq_iff_eq.mpr (by omega)
        have hpw : ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 &&
            rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == pdir (t % 2)) ||
            (fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 &&
              rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == 2 * pdir (t % 2) &&
              rk ((runOf p ms).mv t).src.val == (if t % 2 = 0 then (1 : Int) else 6) &&
              !(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).src.val)
                (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) ||
            ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val).natAbs == 1 &&
              rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == pdir (t % 2))) = true := by
          simp [e1, e2]
        rw [allowed_eq, List.contains_iff_mem, List.mem_filterMap]
        exact ⟨(P, _), List.mem_cons_self, by
          show (if _ then some P else none) = some (kindIdx Kind.pawn)
          rw [if_pos hpw]
          decide⟩
      · obtain ⟨hfx2, hry2, hhome, hdn2, hcl2⟩ := h2
        have e1 : (fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0) = true :=
          beq_iff_eq.mpr (by omega)
        have e2' : (rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val ==
            2 * pdir (t % 2)) = true := beq_iff_eq.mpr (by omega)
        rcases color_parity (t % 2) (Nat.mod_lt _ (by decide)) with ⟨hu, hcol, hpd, hfw, hh⟩ |
          ⟨hu, hcol, hpd, hfw, hh⟩
        · rw [hcol] at hhome hry2
          have hhome2 : ry ((runOf p ms).mv t).src = 1 := hhome.trans (by decide)
          rw [show (Color.white.fwd) = (1 : Int) from rfl] at hry2
          have honbz : onb (fl ((runOf p ms).mv t).src.val)
              (rk ((runOf p ms).mv t).src.val + pdir (t % 2)) = true := by
            simp only [onb, Bool.and_eq_true, decide_eq_true_eq, hpd]
            have b1 := fx_nonneg ((runOf p ms).mv t).src
            have b2 := fx_lt ((runOf p ms).mv t).src
            omega
          obtain ⟨z64, zfl, zrk⟩ := onb_sqOf _ _ honbz
          have hzx : fx (toSq (sqOf (fl ((runOf p ms).mv t).src.val)
              (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) = fx ((runOf p ms).mv t).src := by
            rw [fx_toSq _ z64, zfl]; omega
          have hzy : ry (toSq (sqOf (fl ((runOf p ms).mv t).src.val)
              (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) = ry ((runOf p ms).mv t).src + 1 := by
            rw [ry_toSq _ z64, zrk, hpd]; omega
          have hsegz : inSeg ((runOf p ms).mv t).src ((runOf p ms).mv t).dst (toSq (sqOf
              (fl ((runOf p ms).mv t).src.val) (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) = true := by
            refine inSeg_intro _ _ _
              (bne_iff_ne.mpr (fun he => by have := congrArg ry he; omega))
              (Bool.or_eq_true _ _ |>.mpr (Or.inl
                (Bool.or_eq_true _ _ |>.mpr (Or.inl (beq_iff_eq.mpr hfx2.symm))))) ?_ ?_ ?_
              (beq_iff_eq.mpr (by simp only [kdist]; omega))
            · exact beq_iff_eq.mpr (by
                rw [show fx (toSq (sqOf (fl ((runOf p ms).mv t).src.val)
                      (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) - fx ((runOf p ms).mv t).src = 0
                    from by omega,
                  show fx ((runOf p ms).mv t).dst - fx ((runOf p ms).mv t).src = 0 from by omega,
                  Int.zero_mul, Int.mul_zero])
            · exact bne_iff_ne.mpr (fun he => by have := congrArg ry he; omega)
            · exact bne_iff_ne.mpr (fun he => by have := congrArg ry he; omega)
          have hclz := hcl2 _ hsegz
          have hnok : ∀ cc, ((runOf p ms).pos t).board (toSq (sqOf (fl ((runOf p ms).mv t).src.val)
              (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) ≠ some ⟨cc, .king⟩ := fun cc hh => by
            rw [hclz] at hh; cases hh
          have e4 : (!(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).src.val)
              (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) = true := by
            obtain ⟨hkw, hkb, -⟩ := run_kings h t (Nat.le_of_lt ht)
            rw [isK_false_of_noking _ _ hkw hkb hnok]
            rfl
          have e3 : (rk ((runOf p ms).mv t).src.val == (if t % 2 = 0 then (1 : Int) else 6)) = true :=
            beq_iff_eq.mpr (by rw [hu, if_pos rfl]; omega)
          have hpw : ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 &&
              rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == pdir (t % 2)) ||
              (fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 &&
                rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == 2 * pdir (t % 2) &&
                rk ((runOf p ms).mv t).src.val == (if t % 2 = 0 then (1 : Int) else 6) &&
                !(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).src.val)
                  (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) ||
              ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val).natAbs == 1 &&
                rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == pdir (t % 2))) = true := by
            simp [e1, e2', e3, e4]
          rw [allowed_eq, List.contains_iff_mem, List.mem_filterMap]
          exact ⟨(P, _), List.mem_cons_self, by
            show (if _ then some P else none) = some (kindIdx Kind.pawn)
            rw [if_pos hpw]
            decide⟩
        · rw [hcol] at hhome hry2
          have hhome2 : ry ((runOf p ms).mv t).src = 6 := hhome.trans (by decide)
          rw [show (Color.black.fwd) = (-1 : Int) from rfl] at hry2
          have honbz : onb (fl ((runOf p ms).mv t).src.val)
              (rk ((runOf p ms).mv t).src.val + pdir (t % 2)) = true := by
            simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
            have b1 := fx_nonneg ((runOf p ms).mv t).src
            have b2 := fx_lt ((runOf p ms).mv t).src
            omega
          obtain ⟨z64, zfl, zrk⟩ := onb_sqOf _ _ honbz
          have hzx : fx (toSq (sqOf (fl ((runOf p ms).mv t).src.val)
              (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) = fx ((runOf p ms).mv t).src := by
            rw [fx_toSq _ z64, zfl]; omega
          have hzy : ry (toSq (sqOf (fl ((runOf p ms).mv t).src.val)
              (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) = ry ((runOf p ms).mv t).src - 1 := by
            rw [ry_toSq _ z64, zrk, hpd]; omega
          have hsegz : inSeg ((runOf p ms).mv t).src ((runOf p ms).mv t).dst (toSq (sqOf
              (fl ((runOf p ms).mv t).src.val) (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) = true := by
            refine inSeg_intro _ _ _
              (bne_iff_ne.mpr (fun he => by have := congrArg ry he; omega))
              (Bool.or_eq_true _ _ |>.mpr (Or.inl
                (Bool.or_eq_true _ _ |>.mpr (Or.inl (beq_iff_eq.mpr hfx2.symm))))) ?_ ?_ ?_
              (beq_iff_eq.mpr (by simp only [kdist]; omega))
            · exact beq_iff_eq.mpr (by
                rw [show fx (toSq (sqOf (fl ((runOf p ms).mv t).src.val)
                      (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) - fx ((runOf p ms).mv t).src = 0
                    from by omega,
                  show fx ((runOf p ms).mv t).dst - fx ((runOf p ms).mv t).src = 0 from by omega,
                  Int.zero_mul, Int.mul_zero])
            · exact bne_iff_ne.mpr (fun he => by have := congrArg ry he; omega)
            · exact bne_iff_ne.mpr (fun he => by have := congrArg ry he; omega)
          have hclz := hcl2 _ hsegz
          have hnok : ∀ cc, ((runOf p ms).pos t).board (toSq (sqOf (fl ((runOf p ms).mv t).src.val)
              (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) ≠ some ⟨cc, .king⟩ := fun cc hh => by
            rw [hclz] at hh; cases hh
          have e4 : (!(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).src.val)
              (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) = true := by
            obtain ⟨hkw, hkb, -⟩ := run_kings h t (Nat.le_of_lt ht)
            rw [isK_false_of_noking _ _ hkw hkb hnok]
            rfl
          have e3 : (rk ((runOf p ms).mv t).src.val == (if t % 2 = 0 then (1 : Int) else 6)) = true :=
            beq_iff_eq.mpr (by rw [hu, if_neg (by decide)]; omega)
          have hpw : ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 &&
              rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == pdir (t % 2)) ||
              (fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 &&
                rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == 2 * pdir (t % 2) &&
                rk ((runOf p ms).mv t).src.val == (if t % 2 = 0 then (1 : Int) else 6) &&
                !(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).src.val)
                  (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) ||
              ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val).natAbs == 1 &&
                rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == pdir (t % 2))) = true := by
            simp [e1, e2', e3, e4]
          rw [allowed_eq, List.contains_iff_mem, List.mem_filterMap]
          exact ⟨(P, _), List.mem_cons_self, by
            show (if _ then some P else none) = some (kindIdx Kind.pawn)
            rw [if_pos hpw]
            decide⟩
      · obtain ⟨hatt, -⟩ := h3
        obtain ⟨hry3, hfx3⟩ := pawn_attack_geom _ _ _ _ hatt
        have e1 : ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val).natAbs == 1) =
            true := beq_iff_eq.mpr (by omega)
        have e2 : (rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val ==
            pdir (t % 2)) = true := beq_iff_eq.mpr (by omega)
        have hpw : ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 &&
            rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == pdir (t % 2)) ||
            (fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 &&
              rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == 2 * pdir (t % 2) &&
              rk ((runOf p ms).mv t).src.val == (if t % 2 = 0 then (1 : Int) else 6) &&
              !(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).src.val)
                (rk ((runOf p ms).mv t).src.val + pdir (t % 2)))) ||
            ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val).natAbs == 1 &&
              rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == pdir (t % 2))) = true := by
          simp [e1, e2]
        rw [allowed_eq, List.contains_iff_mem, List.mem_filterMap]
        exact ⟨(P, _), List.mem_cons_self, by
          show (if _ then some P else none) = some (kindIdx Kind.pawn)
          rw [if_pos hpw]
          decide⟩
  | knight =>
      obtain ⟨-, -, hatt⟩ := pieceMoves_geom _ _ _ _ hmem (fun hh => Kind.noConfusion hh)
      have hg : knightJump ((runOf p ms).mv t).src ((runOf p ms).mv t).dst = true :=
        ((mem_attacks_iff _ _ _ _).mp hatt).1
      simp only [knightJump, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at hg
      have hkn : (((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val).natAbs == 1 &&
          (rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val).natAbs == 2) ||
          ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val).natAbs == 2 &&
          (rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val).natAbs == 1)) = true := by
        rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have e1 : ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val).natAbs == 1) =
            true := beq_iff_eq.mpr (by omega)
          have e2 : ((rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val).natAbs == 2) =
            true := beq_iff_eq.mpr (by omega)
          rw [Bool.or_eq_true]
          exact Or.inl (by rw [Bool.and_eq_true]; exact ⟨e1, e2⟩)
        · have e1 : ((fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val).natAbs == 2) =
            true := beq_iff_eq.mpr (by omega)
          have e2 : ((rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val).natAbs == 1) =
            true := beq_iff_eq.mpr (by omega)
          rw [Bool.or_eq_true]
          exact Or.inr (by rw [Bool.and_eq_true]; exact ⟨e1, e2⟩)
      rw [allowed_eq, List.contains_iff_mem, List.mem_filterMap]
      exact ⟨(N, _), List.mem_cons_of_mem _ (List.mem_cons_self), by
        show (if _ then some N else none) = some (kindIdx Kind.knight)
        rw [if_pos hkn]
        decide⟩
  | bishop =>
      obtain ⟨-, -, hatt⟩ := pieceMoves_geom _ _ _ _ hmem (fun hh => Kind.noConfusion hh)
      have hg := (mem_attacks_iff _ _ _ _).mp hatt
      have hg1 : geomAttack c .bishop ((runOf p ms).mv t).src ((runOf p ms).mv t).dst = true := hg.1
      simp only [geomAttack, diagLine, Bool.and_eq_true] at hg1
      obtain ⟨hal, hno0⟩ := hg1
      obtain ⟨l, hbt⟩ := between_some_of_aligned _ _ hal
      have hsl := sl_any_false h t ht (hg.2 rfl) l hbt
      have hX : (fx ((runOf p ms).mv t).src == fx ((runOf p ms).mv t).dst ||
          ry ((runOf p ms).mv t).src == ry ((runOf p ms).mv t).dst) = false := by
        cases hX' : (fx ((runOf p ms).mv t).src == fx ((runOf p ms).mv t).dst ||
          ry ((runOf p ms).mv t).src == ry ((runOf p ms).mv t).dst) with
        | false => rfl
        | true =>
            rw [hX'] at hno0
            exact absurd hno0 (by decide)
      have e1 : (fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0) = false := by
        have hA := beq_eq_false_iff_ne.mp (Bool.or_eq_false_iff.mp hX).1
        exact beq_eq_false_iff_ne.mpr (by omega)
      have e2 : (rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == 0) = false := by
        have hB := beq_eq_false_iff_ne.mp (Bool.or_eq_false_iff.mp hX).2
        exact beq_eq_false_iff_ne.mpr (by omega)
      have hno : (!(fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 ||
          rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == 0)) = true := by
        rw [e1, e2]
        rfl
      have hcond : ((match between ((runOf p ms).mv t).src.val ((runOf p ms).mv t).dst.val with
          | some l => !l.any (cfgOf w b n m).isK | none => false) &&
          !(fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 ||
            rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == 0)) = true := by
        rw [hbt, Bool.and_eq_true]
        refine ⟨?_, hno⟩
        show (!(l.any (cfgOf w b n m).isK)) = true
        rw [hsl]
        rfl
      rw [allowed_eq, List.contains_iff_mem, List.mem_filterMap]
      exact ⟨(B, _), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)), by
        show (if _ then some B else none) = some (kindIdx Kind.bishop)
        rw [if_pos hcond]
        decide⟩
  | rook =>
      obtain ⟨-, -, hatt⟩ := pieceMoves_geom _ _ _ _ hmem (fun hh => Kind.noConfusion hh)
      have hg := (mem_attacks_iff _ _ _ _).mp hatt
      have hg1 : geomAttack c .rook ((runOf p ms).mv t).src ((runOf p ms).mv t).dst = true := hg.1
      simp only [geomAttack, orthLine, Bool.and_eq_true] at hg1
      obtain ⟨hal, ho0⟩ := hg1
      obtain ⟨l, hbt⟩ := between_some_of_aligned _ _ hal
      have hsl := sl_any_false h t ht (hg.2 rfl) l hbt
      have hRo : (fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 ||
          rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == 0) = true := by
        rcases (Bool.or_eq_true ..).mp ho0 with hb | hb
        · have e1 : (fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0) = true :=
            beq_iff_eq.mpr (by have h' := beq_iff_eq.mp hb; omega)
          simp [e1]
        · have e2 : (rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == 0) = true :=
            beq_iff_eq.mpr (by have h' := beq_iff_eq.mp hb; omega)
          simp [e2]
      have hcond : ((match between ((runOf p ms).mv t).src.val ((runOf p ms).mv t).dst.val with
          | some l => !l.any (cfgOf w b n m).isK | none => false) &&
          (fl ((runOf p ms).mv t).dst.val - fl ((runOf p ms).mv t).src.val == 0 ||
            rk ((runOf p ms).mv t).dst.val - rk ((runOf p ms).mv t).src.val == 0)) = true := by
        rw [hbt, Bool.and_eq_true]
        refine ⟨?_, hRo⟩
        show (!(l.any (cfgOf w b n m).isK)) = true
        rw [hsl]
        rfl
      rw [allowed_eq, List.contains_iff_mem, List.mem_filterMap]
      exact ⟨(R, _), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self))), by
        show (if _ then some R else none) = some (kindIdx Kind.rook)
        rw [if_pos hcond]
        decide⟩
  | queen =>
      obtain ⟨-, -, hatt⟩ := pieceMoves_geom _ _ _ _ hmem (fun hh => Kind.noConfusion hh)
      have hg := (mem_attacks_iff _ _ _ _).mp hatt
      have hg1 : geomAttack c .queen ((runOf p ms).mv t).src ((runOf p ms).mv t).dst = true := hg.1
      obtain ⟨l, hbt⟩ := between_some_of_aligned _ _ hg1
      have hsl := sl_any_false h t ht (hg.2 rfl) l hbt
      have hcond : (match between ((runOf p ms).mv t).src.val ((runOf p ms).mv t).dst.val with
          | some l => !l.any (cfgOf w b n m).isK | none => false) = true := by
        rw [hbt]
        show (!(l.any (cfgOf w b n m).isK)) = true
        rw [hsl]
        rfl
      rw [allowed_eq, List.contains_iff_mem, List.mem_filterMap]
      exact ⟨(Q, _), List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))), by
        show (if _ then some Q else none) = some (kindIdx Kind.queen)
        rw [if_pos hcond]
        decide⟩
  | king =>
      have htrue : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .king)) = true := by
        have e : (({ color := c, kind := Kind.king } : Piece).kind == Kind.king) = true := rfl
        rw [hq]
        exact e
      have htrue2 : isKingMove ((runOf p ms).pos t) ((runOf p ms).mv t) = true := htrue
      exact absurd hkm (by rw [htrue2]; decide)

theorem core_transit (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n) :
    ∀ z ∈ btw ((runOf p ms).mv t).src.val ((runOf p ms).mv t).dst.val,
      ((runOf p ms).pos t).board (toSq z) = none := by
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step h t ht
  obtain ⟨q, hq, hqcol, hmem⟩ := legal_nonking_mem _ _ hleg hkm
  obtain ⟨c, k⟩ := q
  intro z hz
  obtain ⟨hz64, hseg⟩ :=
    (mem_btw_iff_nat ((runOf p ms).mv t).src ((runOf p ms).mv t).dst z).mp hz
  cases k with
  | pawn =>
      obtain ⟨-, hdisj, -⟩ := pawnMoves_cases ((runOf p ms).pos t) ((runOf p ms).mv t).src
        c ((runOf p ms).mv t) hmem
      rcases hdisj with h1 | h2 | h3
      · obtain ⟨hfx1, hry1, -⟩ := h1
        have hfw : c.fwd = 1 ∨ c.fwd = -1 := by cases c <;> decide
        have A0 : (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst).natAbs = 0 := by omega
        rcases hfw with hfw | hfw
        · have A1 : (ry ((runOf p ms).mv t).src - ry ((runOf p ms).mv t).dst).natAbs = 1 := by omega
          have hk1 : kdist ((runOf p ms).mv t).src ((runOf p ms).mv t).dst = 1 := by
            simp only [kdist]; rw [A0, A1]; omega
          exact absurd hseg (by rw [inSeg_false_of_kdist_one _ _ _ hk1]; decide)
        · have A1 : (ry ((runOf p ms).mv t).src - ry ((runOf p ms).mv t).dst).natAbs = 1 := by omega
          have hk1 : kdist ((runOf p ms).mv t).src ((runOf p ms).mv t).dst = 1 := by
            simp only [kdist]; rw [A0, A1]; omega
          exact absurd hseg (by rw [inSeg_false_of_kdist_one _ _ _ hk1]; decide)
      · exact h2.2.2.2.2 (toSq z) hseg
      · obtain ⟨hatt, -⟩ := h3
        obtain ⟨hry3, hfx3⟩ := pawn_attack_geom _ _ _ _ hatt
        have hfw : c.fwd = 1 ∨ c.fwd = -1 := by cases c <;> decide
        have A0 : (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst).natAbs = 1 := by omega
        rcases hfw with hfw | hfw
        · have A1 : (ry ((runOf p ms).mv t).src - ry ((runOf p ms).mv t).dst).natAbs = 1 := by omega
          have hk1 : kdist ((runOf p ms).mv t).src ((runOf p ms).mv t).dst = 1 := by
            simp only [kdist]; rw [A0, A1]; omega
          exact absurd hseg (by rw [inSeg_false_of_kdist_one _ _ _ hk1]; decide)
        · have A1 : (ry ((runOf p ms).mv t).src - ry ((runOf p ms).mv t).dst).natAbs = 1 := by omega
          have hk1 : kdist ((runOf p ms).mv t).src ((runOf p ms).mv t).dst = 1 := by
            simp only [kdist]; rw [A0, A1]; omega
          exact absurd hseg (by rw [inSeg_false_of_kdist_one _ _ _ hk1]; decide)
  | knight =>
      obtain ⟨-, -, hatt⟩ := pieceMoves_geom _ _ _ _ hmem (fun hh => Kind.noConfusion hh)
      have hg : knightJump ((runOf p ms).mv t).src ((runOf p ms).mv t).dst = true :=
        ((mem_attacks_iff _ _ _ _).mp hatt).1
      have hna := knightJump_not_aligned _ _ hg
      simp only [inSeg, onLine, Bool.and_eq_true] at hseg
      obtain ⟨⟨⟨⟨hal, -⟩, -⟩, -⟩, -⟩ := hseg
      exact absurd hal (by rw [hna]; decide)
  | bishop =>
      obtain ⟨-, -, hatt⟩ := pieceMoves_geom _ _ _ _ hmem (fun hh => Kind.noConfusion hh)
      exact ((mem_attacks_iff _ _ _ _).mp hatt).2 rfl (toSq z) hseg
  | rook =>
      obtain ⟨-, -, hatt⟩ := pieceMoves_geom _ _ _ _ hmem (fun hh => Kind.noConfusion hh)
      exact ((mem_attacks_iff _ _ _ _).mp hatt).2 rfl (toSq z) hseg
  | queen =>
      obtain ⟨-, -, hatt⟩ := pieceMoves_geom _ _ _ _ hmem (fun hh => Kind.noConfusion hh)
      exact ((mem_attacks_iff _ _ _ _).mp hatt).2 rfl (toSq z) hseg
  | king =>
      have htrue : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .king)) = true := by
        have e : (({ color := c, kind := Kind.king } : Piece).kind == Kind.king) = true := rfl
        rw [hq]
        exact e
      have htrue2 : isKingMove ((runOf p ms).pos t) ((runOf p ms).mv t) = true := htrue
      exact absurd hkm (by rw [htrue2]; decide)

theorem core_pawn (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n)
    (hp : ((runOf p ms).pos t).board ((runOf p ms).mv t).src = some ⟨colorOf (t % 2), .pawn⟩) :
    (fx ((runOf p ms).mv t).src = fx ((runOf p ms).mv t).dst →
      ((runOf p ms).pos t).board ((runOf p ms).mv t).dst = none) ∧
    (fx ((runOf p ms).mv t).src ≠ fx ((runOf p ms).mv t).dst →
      ((runOf p ms).pos t).board ((runOf p ms).mv t).dst ≠ none ∨
        ∃ v, epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some v ∧
          v.val = sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - pdir (t % 2))) := by
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step h t ht
  obtain ⟨q, hq, hqcol, hmem⟩ := legal_nonking_mem _ _ hleg hkm
  have hqX : q = ⟨colorOf (t % 2), Kind.pawn⟩ := by
    have e : some q = some (⟨colorOf (t % 2), Kind.pawn⟩ : Piece) := hq.symm.trans hp
    exact Option.some.inj e
  subst hqX
  obtain ⟨-, hdisj, -⟩ := pawnMoves_cases ((runOf p ms).pos t) ((runOf p ms).mv t).src
    (colorOf (t % 2)) ((runOf p ms).mv t) hmem
  constructor
  · intro hfx
    rcases hdisj with h1 | h2 | h3
    · exact h1.2.2
    · exact h2.2.2.2.1
    · obtain ⟨hatt, -⟩ := h3
      obtain ⟨hry3, hfx3⟩ := pawn_attack_geom _ _ _ _ hatt
      exact absurd (show (fx ((runOf p ms).mv t).dst - fx ((runOf p ms).mv t).src).natAbs = 1 from hfx3)
        (by omega)
  · intro hfx
    rcases hdisj with h1 | h2 | h3
    · exact absurd h1.1.symm hfx
    · exact absurd h2.1.symm hfx
    · obtain ⟨hatt, hfo⟩ := h3
      rcases hfo with hfoe | hec
      · left
        intro hb
        simp [foe, hb] at hfoe
      · right
        obtain ⟨hry3, hfx3⟩ := pawn_attack_geom _ _ _ _ hatt
        have hdn := epCap_none _ _ _ hec
        refine ⟨sq ((runOf p ms).mv t).dst.file ((runOf p ms).mv t).src.rank, ?_, ?_⟩
        · have hcond : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn) &&
              ((runOf p ms).mv t).src.file != ((runOf p ms).mv t).dst.file &&
              empty ((runOf p ms).pos t).board ((runOf p ms).mv t).dst) = true := by
            rw [Bool.and_eq_true, Bool.and_eq_true]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · have e : ((⟨colorOf (t % 2), Kind.pawn⟩ : Piece).kind == Kind.pawn) = true := rfl
              rw [hp]
              exact e
            · exact bne_iff_ne.mpr (fun he => hfx (congrArg (fun x : Nat => (x : Int)) he))
            · show (((runOf p ms).pos t).board ((runOf p ms).mv t).dst).isNone = true
              rw [hdn]
              rfl
          rw [epVictim_eq, if_pos hcond]
        · have hfwd : pdir (t % 2) = (colorOf (t % 2)).fwd := by
            rcases color_parity (t % 2) (Nat.mod_lt _ (by decide)) with ⟨_, _, hpd, hfw, _⟩ |
              ⟨_, _, hpd, hfw, _⟩ <;> rw [hpd, hfw]
          have hvv : (sq ((runOf p ms).mv t).dst.file ((runOf p ms).mv t).src.rank).val =
              ((runOf p ms).mv t).src.rank * 8 + ((runOf p ms).mv t).dst.file := by
            show (((runOf p ms).mv t).src.rank * 8 + ((runOf p ms).mv t).dst.file) % 64 =
              ((runOf p ms).mv t).src.rank * 8 + ((runOf p ms).mv t).dst.file
            have h1 : ((runOf p ms).mv t).src.rank < 8 := by
              have hlt := ((runOf p ms).mv t).src.isLt
              show ((runOf p ms).mv t).src.val / 8 < 8
              omega
            have h2 : ((runOf p ms).mv t).dst.file < 8 := Nat.mod_lt _ (by decide)
            omega
          rw [hvv]
          have hY : rk ((runOf p ms).mv t).dst.val - pdir (t % 2) =
              (((runOf p ms).mv t).src.rank : Int) := by
            have e : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
            have e2 : ry ((runOf p ms).mv t).src = (((runOf p ms).mv t).src.rank : Int) := rfl
            rw [e, hfwd, hry3]
            omega
          show ((runOf p ms).mv t).src.rank * 8 + ((runOf p ms).mv t).dst.file =
            (fl ((runOf p ms).mv t).dst.val + 8 * (rk ((runOf p ms).mv t).dst.val - pdir (t % 2))).toNat
          rw [hY]
          have hnn : (0 : Int) ≤ fl ((runOf p ms).mv t).dst.val + 8 *
              (((runOf p ms).mv t).src.rank : Int) := by
            have h1 := fx_nonneg ((runOf p ms).mv t).dst
            have h2 := ry_nonneg ((runOf p ms).mv t).src
            have lfd : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl
            omega
          have hcast := Int.toNat_of_nonneg hnn
          apply Int.ofNat_inj.mp
          rw [hcast]
          have lfd : fl ((runOf p ms).mv t).dst.val = ((((runOf p ms).mv t).dst.file : Nat) : Int) := rfl
          have e2 : ry ((runOf p ms).mv t).src = (((runOf p ms).mv t).src.rank : Int) := rfl
          omega

theorem core_ep0 (h : ChainAt w b n m p ms) (s : Sq) (hs : ((runOf p ms).pos 0).ep = some s) :
    s.val ∈ epSquares (cfgOf w b n m) 0 ∧ epOk ((runOf p ms).pos 0) s := by
  obtain ⟨hc0, hturn, hkw, hkb, hkf, hlen, hcaps⟩ := h
  have hep : epOk p s := hc0.ep s hs
  obtain ⟨hr5, hsn, ⟨o, hoffo, hon⟩, ⟨d, hoffd, hdb⟩⟩ := hep
  have hfw : p.turn.fwd = 1 := by rw [hturn]; decide
  have hry5 : ry s = 5 := by
    have e : (if p.turn = .white then (5 : Int) else 2) = 5 := by rw [hturn]; decide
    exact hr5.trans e
  obtain ⟨hfox, hroy⟩ := (off_eq_some s o 0 p.turn.fwd).mp hoffo
  obtain ⟨hfod, hrod⟩ := (off_eq_some s d 0 (-p.turn.fwd)).mp hoffd
  rw [hfw] at hroy hrod
  have hroy6 : ry o = 6 := by omega
  have hrod4 : ry d = 4 := by omega
  have hdb2 : p.board d = some ⟨.black, .pawn⟩ := by
    rw [hturn] at hdb
    exact hdb
  have lf5 : rk s.val = 5 := by have e : rk s.val = ry s := rfl; rw [e, hry5]
  have lfx : fl s.val = fx s := rfl
  have lry : rk s.val = ry s := rfl
  have b1 := fx_nonneg s
  have b2 := fx_lt s
  have honb_m : onb (fl s.val) (rk s.val - 1) = true := by
    simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have honb_p : onb (fl s.val) (rk s.val + 1) = true := by
    simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hzd : toSq (sqOf (fl s.val) (rk s.val - 1)) = d :=
    toSq_sqOf_eq d _ _ honb_m (by omega) (by omega)
  have hzo : toSq (sqOf (fl s.val) (rk s.val + 1)) = o :=
    toSq_sqOf_eq o _ _ honb_p (by omega) (by omega)
  constructor
  · rw [epSquares_eq]
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · refine List.mem_filter.mpr ⟨List.mem_range.mpr s.isLt, ?_⟩
      show (!(cfgOf w b n m).isK s.val) = true
      have hnok : ∀ c, p.board (toSq s.val) ≠ some ⟨c, .king⟩ := fun c hh => by
        rw [toSq_val, hsn] at hh; cases hh
      rw [isK_false_of_noking p s.val hkw hkb hnok]
      rfl
    · show (rk s.val == (if (cfgOf w b n m).col 0 = 0 then (5 : Int) else 2) &&
          !(cfgOf w b n m).isK (sqOf (fl s.val) (rk s.val - pdir ((cfgOf w b n m).col 0))) &&
          !(cfgOf w b n m).isK (sqOf (fl s.val) (rk s.val + pdir ((cfgOf w b n m).col 0)))) = true
      have hcol0 : (cfgOf w b n m).col 0 = 0 := rfl
      rw [hcol0, show pdir (0 : Nat) = 1 from rfl, show (if (0 : Nat) = 0 then (5 : Int) else 2) = 5 from rfl]
      have hc1 : (rk s.val == 5) = true := beq_iff_eq.mpr lf5
      have hc2 : (!(cfgOf w b n m).isK (sqOf (fl s.val) (rk s.val - 1))) = true := by
        have hnok : ∀ c, p.board (toSq (sqOf (fl s.val) (rk s.val - 1))) ≠ some ⟨c, .king⟩ :=
          fun c hh => by rw [hzd, hdb2] at hh; cases hh
        rw [isK_false_of_noking p _ hkw hkb hnok]
        rfl
      have hc3 : (!(cfgOf w b n m).isK (sqOf (fl s.val) (rk s.val + 1))) = true := by
        have hnok : ∀ c, p.board (toSq (sqOf (fl s.val) (rk s.val + 1))) ≠ some ⟨c, .king⟩ :=
          fun c hh => by rw [hzo, hon] at hh; cases hh
        rw [isK_false_of_noking p _ hkw hkb hnok]
        rfl
      rw [hc1, hc2, hc3]
      rfl
  · exact hc0.ep s hs

theorem toSq_file_rank (x : Nat) (hx : x < 64) : (toSq x).file = x % 8 ∧ (toSq x).rank = x / 8 := by
  simp only [toSq, Sq.file, Sq.rank]
  omega

theorem core_eps (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n) (s : Nat)
    (hs : s ∈ epSquares (cfgOf w b n m) (t + 1)) :
    ((runOf p ms).pos (t + 1)).ep = some (toSq s) ↔
      (((runOf p ms).mv t).src.val = sqOf (fl s) (rk s + pdir ((t + 1) % 2)) ∧
        ((runOf p ms).mv t).dst.val = sqOf (fl s) (rk s - pdir ((t + 1) % 2)) ∧
        (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn) = true) := by
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step h t ht
  have ht62 : (t + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [epSquares_eq] at hs
  obtain ⟨hNK, hcond0⟩ := List.mem_filter.mp hs
  obtain ⟨hsr, -⟩ := List.mem_filter.mp hNK
  have hs64 : s < 64 := List.mem_range.mp hsr
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond0
  obtain ⟨⟨hrk, -⟩, -⟩ := hcond0
  have hrk' : rk s = if (t + 1) % 2 = 0 then (5 : Int) else 2 := hrk
  have hm8 : s % 8 < 8 := Nat.mod_lt _ (by decide)
  have efls : fl s = ((s % 8 : Nat) : Int) := rfl
  rcases color_parity ((t + 1) % 2) ht62 with ⟨he, hcol, hpd, hfw, hh⟩ | ⟨he, hcol, hpd, hfw, hh⟩
  · have hrk5 : rk s = 5 := by rw [he] at hrk'; exact hrk'
    have htu : t % 2 = 1 := by omega
    have hmp : colorOf (t % 2) = .black := by rw [htu]; decide
    have hfwd : (colorOf (t % 2)).fwd = (-1 : Int) := by rw [htu]; decide
    constructor
    · intro hsep
      rw [hstep, play_ep] at hsep
      by_cases hcef : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn) &&
          (((runOf p ms).mv t).src.rank + 2 == ((runOf p ms).mv t).dst.rank ||
          ((runOf p ms).mv t).dst.rank + 2 == ((runOf p ms).mv t).src.rank)) = true
      · rw [if_pos hcef] at hsep
        obtain ⟨hA, hB⟩ := (Bool.and_eq_true _ _).mp hcef
        have hrank2 := (Bool.or_eq_true _ _).mp hB
        have hsqi := Option.some.inj hsep
        have hmidlt : (((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2 < 8 := by
          have h1 := ((runOf p ms).mv t).src.isLt
          have h2 := ((runOf p ms).mv t).dst.isLt
          show (((runOf p ms).mv t).src.val / 8 + ((runOf p ms).mv t).dst.val / 8) / 2 < 8
          omega
        have hF8 : ((runOf p ms).mv t).src.file < 8 := Nat.mod_lt _ (by decide)
        have hfs : (sq ((runOf p ms).mv t).src.file
            ((((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2)).file =
            ((runOf p ms).mv t).src.file := file_sq _ _ hF8 hmidlt
        have hrs : (sq ((runOf p ms).mv t).src.file
            ((((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2)).rank =
            (((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2 := rank_sq _ _ hF8 hmidlt
        have e1 : ((runOf p ms).mv t).src.file = s % 8 := by
          have e := congrArg Sq.file hsqi
          rw [hfs, (toSq_file_rank s hs64).1] at e
          exact e
        have e2 : (((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2 = s / 8 := by
          have e := congrArg Sq.rank hsqi
          rw [hrs, (toSq_file_rank s hs64).2] at e
          exact e
        obtain ⟨q, hq, hqcol, hmem⟩ := legal_nonking_mem _ _ hleg hkm
        obtain ⟨cq, kq⟩ := q
        have hkp : kq = .pawn := by
          have e : (kq == Kind.pawn) = true := by
            have e2 := hA
            rw [hq] at e2
            exact e2
          exact beq_iff_eq.mp e
        subst hkp
        obtain ⟨-, hdisj, -⟩ := pawnMoves_cases ((runOf p ms).pos t) ((runOf p ms).mv t).src
          cq ((runOf p ms).mv t) hmem
        have hcqc : cq = ((runOf p ms).pos t).turn := hqcol
        have hcqC : cq = colorOf (t % 2) := hcqc.trans (run_turn h t (Nat.le_of_lt ht))
        have hcq : cq = Color.black := hcqC.trans hmp
        subst hcq
        rw [show (Color.black.fwd) = (-1 : Int) from rfl] at hdisj
        have rys : ry ((runOf p ms).mv t).src = (((runOf p ms).mv t).src.rank : Int) := rfl
        have hyd : ry ((runOf p ms).mv t).dst = (((runOf p ms).mv t).dst.rank : Int) := rfl
        have hrk5' : ((s / 8 : Nat) : Int) = 5 := by have e : rk s = ((s / 8 : Nat) : Int) := rfl; omega
        have hs5 : s / 8 = 5 := by omega
        rcases hdisj with hd1 | hd2 | hd3
        · rcases hrank2 with hr | hr
          · have := beq_iff_eq.mp hr; omega
          · have := beq_iff_eq.mp hr; omega
        · obtain ⟨hfx2, hry2, hhome, hdn2, hcl2⟩ := hd2
          have hsrc6 : ry ((runOf p ms).mv t).src = 6 := hhome.trans (by decide)
          have hd4 : ry ((runOf p ms).mv t).dst = 4 := by omega
          have hfls : fl s = fl ((runOf p ms).mv t).src.val := by
            have e : fl ((runOf p ms).mv t).src.val = ((((runOf p ms).mv t).src.file : Nat) : Int) := rfl
            have ei : ((s % 8 : Nat) : Int) = ((((runOf p ms).mv t).src.file : Nat) : Int) := by omega
            omega
          have hfls2 : fl s = fl ((runOf p ms).mv t).dst.val := by
            have ei : fl ((runOf p ms).mv t).src.val = fl ((runOf p ms).mv t).dst.val := by
              have a : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
              have b : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl
              omega
            omega
          have hrkA : rk s + pdir ((t + 1) % 2) = rk ((runOf p ms).mv t).src.val := by
            rw [hpd, hrk5]
            have e : rk ((runOf p ms).mv t).src.val = ry ((runOf p ms).mv t).src := rfl
            rw [e]; omega
          have hrkB : rk s - pdir ((t + 1) % 2) = rk ((runOf p ms).mv t).dst.val := by
            rw [hpd, hrk5]
            have e : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
            rw [e]; omega
          exact ⟨by rw [hfls, hrkA]; exact (fl_rk_sqOf _).symm,
            by rw [hfls2, hrkB]; exact (fl_rk_sqOf _).symm, hA⟩
        · obtain ⟨hatt, -⟩ := hd3
          obtain ⟨hry3, hfx3⟩ := pawn_attack_geom _ _ _ Color.black hatt
          rw [show (Color.black.fwd) = (-1 : Int) from rfl] at hry3
          rcases hrank2 with hr | hr
          · have := beq_iff_eq.mp hr; omega
          · have := beq_iff_eq.mp hr; omega
      · rw [if_neg hcef] at hsep
        cases hsep
    · rintro ⟨h1, h2, h3⟩
      have honb1 : onb (fl s) (rk s + pdir ((t + 1) % 2)) = true := by
        rw [hpd, hrk5]
        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
        omega
      have honb2 : onb (fl s) (rk s - pdir ((t + 1) % 2)) = true := by
        rw [hpd, hrk5]
        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
        omega
      obtain ⟨zb1, za1, zc1⟩ := onb_sqOf _ _ honb1
      obtain ⟨zb2, za2, zc2⟩ := onb_sqOf _ _ honb2
      have hsrcrk : ((runOf p ms).mv t).src.rank = 6 := by
        have e := congrArg rk h1
        rw [zc1, hpd, hrk5] at e
        have link : rk ((runOf p ms).mv t).src.val = ((((runOf p ms).mv t).src.rank : Nat) : Int) := rfl
        omega
      have hdstrk : ((runOf p ms).mv t).dst.rank = 4 := by
        have e := congrArg rk h2
        rw [zc2, hpd, hrk5] at e
        have link : rk ((runOf p ms).mv t).dst.val = ((((runOf p ms).mv t).dst.rank : Nat) : Int) := rfl
        omega
      have hsrcfl : ((runOf p ms).mv t).src.file = s % 8 := by
        have e := congrArg fl h1
        rw [za1] at e
        have link : fl ((runOf p ms).mv t).src.val = ((((runOf p ms).mv t).src.file : Nat) : Int) := rfl
        omega
      have hrc : (((runOf p ms).mv t).src.rank + 2 == ((runOf p ms).mv t).dst.rank ||
          ((runOf p ms).mv t).dst.rank + 2 == ((runOf p ms).mv t).src.rank) = true := by
        rw [hsrcrk, hdstrk]; decide
      have hcefb : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn) &&
          (((runOf p ms).mv t).src.rank + 2 == ((runOf p ms).mv t).dst.rank ||
          ((runOf p ms).mv t).dst.rank + 2 == ((runOf p ms).mv t).src.rank)) = true :=
        (Bool.and_eq_true _ _).mpr ⟨h3, hrc⟩
      rw [hstep, play_ep, if_pos hcefb]
      have hs5 : s / 8 = 5 := by
        have e : rk s = ((s / 8 : Nat) : Int) := rfl
        omega
      have hfin : sq ((runOf p ms).mv t).src.file
          ((((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2) = toSq s := by
        apply Fin.ext
        show ((((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2 * 8 +
          ((runOf p ms).mv t).src.file) % 64 = s % 64
        rw [hsrcrk, hdstrk, hsrcfl]
        omega
      exact congrArg some hfin
  · have hrk2 : rk s = 2 := by rw [he] at hrk'; exact hrk'
    have htu : t % 2 = 0 := by omega
    have hmp : colorOf (t % 2) = .white := by rw [htu]; decide
    have hfwd : (colorOf (t % 2)).fwd = (1 : Int) := by rw [htu]; decide
    constructor
    · intro hsep
      rw [hstep, play_ep] at hsep
      by_cases hcef : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn) &&
          (((runOf p ms).mv t).src.rank + 2 == ((runOf p ms).mv t).dst.rank ||
          ((runOf p ms).mv t).dst.rank + 2 == ((runOf p ms).mv t).src.rank)) = true
      · rw [if_pos hcef] at hsep
        obtain ⟨hA, hB⟩ := (Bool.and_eq_true _ _).mp hcef
        have hrank2 := (Bool.or_eq_true _ _).mp hB
        have hsqi := Option.some.inj hsep
        have hmidlt : (((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2 < 8 := by
          have h1 := ((runOf p ms).mv t).src.isLt
          have h2 := ((runOf p ms).mv t).dst.isLt
          show (((runOf p ms).mv t).src.val / 8 + ((runOf p ms).mv t).dst.val / 8) / 2 < 8
          omega
        have hF8 : ((runOf p ms).mv t).src.file < 8 := Nat.mod_lt _ (by decide)
        have hfs : (sq ((runOf p ms).mv t).src.file
            ((((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2)).file =
            ((runOf p ms).mv t).src.file := file_sq _ _ hF8 hmidlt
        have hrs : (sq ((runOf p ms).mv t).src.file
            ((((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2)).rank =
            (((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2 := rank_sq _ _ hF8 hmidlt
        have e1 : ((runOf p ms).mv t).src.file = s % 8 := by
          have e := congrArg Sq.file hsqi
          rw [hfs, (toSq_file_rank s hs64).1] at e
          exact e
        have e2 : (((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2 = s / 8 := by
          have e := congrArg Sq.rank hsqi
          rw [hrs, (toSq_file_rank s hs64).2] at e
          exact e
        obtain ⟨q, hq, hqcol, hmem⟩ := legal_nonking_mem _ _ hleg hkm
        obtain ⟨cq, kq⟩ := q
        have hkp : kq = .pawn := by
          have e : (kq == Kind.pawn) = true := by
            have e2 := hA
            rw [hq] at e2
            exact e2
          exact beq_iff_eq.mp e
        subst hkp
        obtain ⟨-, hdisj, -⟩ := pawnMoves_cases ((runOf p ms).pos t) ((runOf p ms).mv t).src
          cq ((runOf p ms).mv t) hmem
        have hcqc : cq = ((runOf p ms).pos t).turn := hqcol
        have hcqC : cq = colorOf (t % 2) := hcqc.trans (run_turn h t (Nat.le_of_lt ht))
        have hcq : cq = Color.white := hcqC.trans hmp
        subst hcq
        rw [show (Color.white.fwd) = (1 : Int) from rfl] at hdisj
        have rys : ry ((runOf p ms).mv t).src = (((runOf p ms).mv t).src.rank : Int) := rfl
        have hyd : ry ((runOf p ms).mv t).dst = (((runOf p ms).mv t).dst.rank : Int) := rfl
        have hrk2' : ((s / 8 : Nat) : Int) = 2 := by have e : rk s = ((s / 8 : Nat) : Int) := rfl; omega
        have hs2 : s / 8 = 2 := by omega
        rcases hdisj with hd1 | hd2 | hd3
        · rcases hrank2 with hr | hr
          · have := beq_iff_eq.mp hr; omega
          · have := beq_iff_eq.mp hr; omega
        · obtain ⟨hfx2, hry2, hhome, hdn2, hcl2⟩ := hd2
          have hsrc1 : ry ((runOf p ms).mv t).src = 1 := hhome.trans (by decide)
          have hd3' : ry ((runOf p ms).mv t).dst = 3 := by omega
          have hfls : fl s = fl ((runOf p ms).mv t).src.val := by
            have e : fl ((runOf p ms).mv t).src.val = ((((runOf p ms).mv t).src.file : Nat) : Int) := rfl
            have ei : ((s % 8 : Nat) : Int) = ((((runOf p ms).mv t).src.file : Nat) : Int) := by omega
            omega
          have hfls2 : fl s = fl ((runOf p ms).mv t).dst.val := by
            have ei : fl ((runOf p ms).mv t).src.val = fl ((runOf p ms).mv t).dst.val := by
              have a : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
              have b : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl
              omega
            omega
          have hrkA : rk s + pdir ((t + 1) % 2) = rk ((runOf p ms).mv t).src.val := by
            rw [hpd, hrk2]
            have e : rk ((runOf p ms).mv t).src.val = ry ((runOf p ms).mv t).src := rfl
            rw [e]; omega
          have hrkB : rk s - pdir ((t + 1) % 2) = rk ((runOf p ms).mv t).dst.val := by
            rw [hpd, hrk2]
            have e : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
            rw [e]; omega
          exact ⟨by rw [hfls, hrkA]; exact (fl_rk_sqOf _).symm,
            by rw [hfls2, hrkB]; exact (fl_rk_sqOf _).symm, hA⟩
        · obtain ⟨hatt, -⟩ := hd3
          obtain ⟨hry3, hfx3⟩ := pawn_attack_geom _ _ _ Color.white hatt
          rw [show (Color.white.fwd) = (1 : Int) from rfl] at hry3
          rcases hrank2 with hr | hr
          · have := beq_iff_eq.mp hr; omega
          · have := beq_iff_eq.mp hr; omega
      · rw [if_neg hcef] at hsep
        cases hsep
    · rintro ⟨h1, h2, h3⟩
      have honb1 : onb (fl s) (rk s + pdir ((t + 1) % 2)) = true := by
        rw [hpd, hrk2]
        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
        omega
      have honb2 : onb (fl s) (rk s - pdir ((t + 1) % 2)) = true := by
        rw [hpd, hrk2]
        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
        omega
      obtain ⟨zb1, za1, zc1⟩ := onb_sqOf _ _ honb1
      obtain ⟨zb2, za2, zc2⟩ := onb_sqOf _ _ honb2
      have hsrcrk : ((runOf p ms).mv t).src.rank = 1 := by
        have e := congrArg rk h1
        rw [zc1, hpd, hrk2] at e
        have link : rk ((runOf p ms).mv t).src.val = ((((runOf p ms).mv t).src.rank : Nat) : Int) := rfl
        omega
      have hdstrk : ((runOf p ms).mv t).dst.rank = 3 := by
        have e := congrArg rk h2
        rw [zc2, hpd, hrk2] at e
        have link : rk ((runOf p ms).mv t).dst.val = ((((runOf p ms).mv t).dst.rank : Nat) : Int) := rfl
        omega
      have hsrcfl : ((runOf p ms).mv t).src.file = s % 8 := by
        have e := congrArg fl h1
        rw [za1] at e
        have link : fl ((runOf p ms).mv t).src.val = ((((runOf p ms).mv t).src.file : Nat) : Int) := rfl
        omega
      have hrc : (((runOf p ms).mv t).src.rank + 2 == ((runOf p ms).mv t).dst.rank ||
          ((runOf p ms).mv t).dst.rank + 2 == ((runOf p ms).mv t).src.rank) = true := by
        rw [hsrcrk, hdstrk]; decide
      have hcefb : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn) &&
          (((runOf p ms).mv t).src.rank + 2 == ((runOf p ms).mv t).dst.rank ||
          ((runOf p ms).mv t).dst.rank + 2 == ((runOf p ms).mv t).src.rank)) = true :=
        (Bool.and_eq_true _ _).mpr ⟨h3, hrc⟩
      rw [hstep, play_ep, if_pos hcefb]
      have hs2 : s / 8 = 2 := by
        have e : rk s = ((s / 8 : Nat) : Int) := rfl
        omega
      have hfin : sq ((runOf p ms).mv t).src.file
          ((((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2) = toSq s := by
        apply Fin.ext
        show ((((runOf p ms).mv t).src.rank + ((runOf p ms).mv t).dst.rank) / 2 * 8 +
          ((runOf p ms).mv t).src.file) % 64 = s % 64
        rw [hsrcrk, hdstrk, hsrcfl]
        omega
      exact congrArg some hfin

theorem core_epr (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n) (v : Sq)
    (hv : epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some v) :
    ∃ e, (v.val, e) ∈ eprSquares (cfgOf w b n m) t
      ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []) := by
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step h t ht
  obtain ⟨hep, hdn0, hvb, hfxv, hryv, hsrc⟩ := epVictim_spec _ _ _ hleg hv
  obtain ⟨hkw, hkb, hkk⟩ := run_kings h t (Nat.le_of_lt ht)
  have hturn := run_turn h t (Nat.le_of_lt ht)
  obtain ⟨hr5, hdtn, ⟨o, hoo, hon⟩, ⟨d, hod, hdb⟩⟩ := (run_c0 h t (Nat.le_of_lt ht)).ep _ hep
  rw [epVictim_eq] at hv
  have hfn : ((runOf p ms).mv t).src.file ≠ ((runOf p ms).mv t).dst.file := by
    by_cases hc : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn) &&
        ((runOf p ms).mv t).src.file != ((runOf p ms).mv t).dst.file &&
        empty ((runOf p ms).pos t).board ((runOf p ms).mv t).dst) = true
    · rw [if_pos hc] at hv
      exact bne_iff_ne.mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hc).1).2
    · rw [if_neg hc] at hv
      cases hv
  have hfnI : fx ((runOf p ms).mv t).src ≠ fx ((runOf p ms).mv t).dst := by
    intro he
    exact hfn (Int.ofNat_inj.mp he)
  obtain ⟨q, hq, hqcol, hmem⟩ := legal_nonking_mem _ _ hleg hkm
  have hqX : q = ⟨((runOf p ms).pos t).turn, Kind.pawn⟩ := by
    have e : some q = some (⟨((runOf p ms).pos t).turn, Kind.pawn⟩ : Piece) := hq.symm.trans hsrc
    exact Option.some.inj e
  subst hqX
  obtain ⟨-, hdisj, -⟩ := pawnMoves_cases ((runOf p ms).pos t) ((runOf p ms).mv t).src
    ((runOf p ms).pos t).turn ((runOf p ms).mv t) hmem
  rcases hdisj with hd1 | hd2 | hd3
  · exact absurd hd1.1.symm hfnI
  · exact absurd hd2.1.symm hfnI
  · obtain ⟨hatt, hfo⟩ := hd3
    rcases hfo with hfoe | hec
    · simp [foe, hdn0] at hfoe
    · obtain ⟨hry3, hfx3⟩ := pawn_attack_geom _ _ _ _ hatt
      rcases color_parity (t % 2) (Nat.mod_lt _ (by decide)) with ⟨hu, hcol, hpd, hfw, hh⟩ |
        ⟨hu, hcol, hpd, hfw, hh⟩
      · have htw : ((runOf p ms).pos t).turn = .white := hturn.trans hcol
        have hrdT : ry ((runOf p ms).mv t).dst = (5 : Int) := hr5.trans (by rw [htw]; decide)
        rw [show ((runOf p ms).pos t).turn.fwd = (1 : Int) from by rw [htw]; decide] at hry3
        have hsrcR : ry ((runOf p ms).mv t).src = (4 : Int) := by omega
        have hrv : ry v = (4 : Int) := by omega
        have hcolt : (cfgOf w b n m).col t = 0 := hu
        have hrr : rk v.val = (if (cfgOf w b n m).col t = 0 then (4 : Int) else 3) := by
          rw [hcolt, show (if ((0 : Nat) : Nat) = 0 then (4 : Int) else 3) = (4 : Int) from rfl]
          have e : rk v.val = ry v := rfl
          omega
        have hNKv : v.val ∈ (cfgOf w b n m).NK := by
          refine List.mem_filter.mpr ⟨List.mem_range.mpr v.isLt, ?_⟩
          show (!(cfgOf w b n m).isK v.val) = true
          have hnok : ∀ c, ((runOf p ms).pos t).board (toSq v.val) ≠ some ⟨c, .king⟩ :=
            fun c hh => by rw [toSq_val, hvb] at hh; cases hh
          rw [isK_false_of_noking _ _ hkw hkb hnok]
          rfl
        obtain ⟨hE1, -⟩ := roles_eps (g := cfgOf w b n m) t (Nat.le_of_lt ht)
        have hgq : sqOf (fl v.val) (rk v.val + pdir ((cfgOf w b n m).col t)) =
            ((runOf p ms).mv t).dst.val := by
          rw [hcolt, show pdir (0 : Nat) = (1 : Int) from rfl]
          have h1' : fl v.val = fl ((runOf p ms).mv t).dst.val := by
            have a : fl v.val = fx v := rfl
            have b : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl
            omega
          have h2' : rk v.val + (1 : Int) = rk ((runOf p ms).mv t).dst.val := by
            have a : rk v.val = ry v := rfl
            have b : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
            omega
          rw [← fl_rk_sqOf (((runOf p ms).mv t).dst.val), h1', h2']
        have hdstNK : ((runOf p ms).mv t).dst.val ∈ (cfgOf w b n m).NK := by
          refine List.mem_filter.mpr ⟨List.mem_range.mpr ((runOf p ms).mv t).dst.isLt, ?_⟩
          show (!(cfgOf w b n m).isK ((runOf p ms).mv t).dst.val) = true
          have hnok : ∀ c, ((runOf p ms).pos t).board (toSq ((runOf p ms).mv t).dst.val) ≠ some ⟨c, .king⟩ :=
            fun c hh => by rw [toSq_val, hdn0] at hh; cases hh
          rw [isK_false_of_noking _ _ hkw hkb hnok]
          rfl
        have honbm : onb (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - (1 : Int)) = true := by
          simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
          have a : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl
          have b : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
          have b1 := fx_nonneg ((runOf p ms).mv t).dst
          have b2 := fx_lt ((runOf p ms).mv t).dst
          omega
        have honbp : onb (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val + (1 : Int)) = true := by
          simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
          have a : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl
          have b : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
          have b1 := fx_nonneg ((runOf p ms).mv t).dst
          have b2 := fx_lt ((runOf p ms).mv t).dst
          omega
        obtain ⟨hfox, hroy⟩ := (off_eq_some ((runOf p ms).mv t).dst o 0 ((runOf p ms).pos t).turn.fwd).mp hoo
        rw [show ((runOf p ms).pos t).turn.fwd = (1 : Int) from by rw [htw]; decide] at hroy
        have hsvm : toSq (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - (1 : Int))) = v :=
          toSq_sqOf_eq v _ _ honbm (by have a : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl; omega)
            (by have b : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl; omega)
        have hsvp : toSq (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val + (1 : Int))) = o :=
          toSq_sqOf_eq o _ _ honbp (by have a : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl; omega)
            (by have b : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl; omega)
        have hmemg : ((runOf p ms).mv t).dst.val ∈ epSquares (cfgOf w b n m) t := by
          rw [epSquares_eq]
          refine List.mem_filter.mpr ⟨hdstNK, ?_⟩
          show (rk ((runOf p ms).mv t).dst.val == (if (cfgOf w b n m).col t = 0 then (5 : Int) else 2) &&
            !(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - pdir ((cfgOf w b n m).col t))) &&
            !(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val + pdir ((cfgOf w b n m).col t)))) = true
          rw [hcolt, show pdir (0 : Nat) = (1 : Int) from rfl, show (if ((0 : Nat) : Nat) = 0 then (5 : Int) else 2) = (5 : Int) from rfl]
          have hc1 : (rk ((runOf p ms).mv t).dst.val == (5 : Int)) = true := by
            apply beq_iff_eq.mpr
            have e : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
            omega
          have hc2 : (!(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - (1 : Int)))) = true := by
            have hnok : ∀ c, ((runOf p ms).pos t).board (toSq (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - (1 : Int)))) ≠ some ⟨c, .king⟩ :=
              fun c hh => by rw [hsvm, hvb] at hh; cases hh
            rw [isK_false_of_noking _ _ hkw hkb hnok]
            rfl
          have hc3 : (!(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val + (1 : Int)))) = true := by
            have hnok : ∀ c, ((runOf p ms).pos t).board (toSq (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val + (1 : Int)))) ≠ some ⟨c, .king⟩ :=
              fun c hh => by rw [hsvp, hon] at hh; cases hh
            rw [isK_false_of_noking _ _ hkw hkb hnok]
            rfl
          rw [hc1, hc2, hc3]
          rfl
        obtain ⟨kv, hkvE, hkv1⟩ := List.mem_map.mp (show ((runOf p ms).mv t).dst.val ∈
          (((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []).map (·.1)) from hE1 ▸ hmemg)
        have hlkf : (look ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []) ((runOf p ms).mv t).dst.val).isNone = false := by
          show ((((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []).find? (·.1 == ((runOf p ms).mv t).dst.val)).map (·.2)).isNone = false
          cases hfind : ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []).find? (·.1 == ((runOf p ms).mv t).dst.val) with
          | none =>
              exfalso
              rw [List.find?_eq_none] at hfind
              exact hfind kv hkvE (beq_iff_eq.mpr hkv1)
          | some kv' => rfl
        have hdf : fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst = 1 ∨
            fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst = -1 := by omega
        have hF1 : fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst) =
            fl ((runOf p ms).mv t).src.val := by
          have a : fl v.val = fx v := rfl
          have b : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
          omega
        have hR1 : rk v.val = rk ((runOf p ms).mv t).src.val := by
          have a : rk v.val = ry v := rfl
          have b : rk ((runOf p ms).mv t).src.val = ry ((runOf p ms).mv t).src := rfl
          omega
        have hsqD : sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val) =
            ((runOf p ms).mv t).src.val := by
          rw [hF1, hR1, fl_rk_sqOf]
        have honbD : onb (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val) = true := by
          rw [hF1]
          simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
          have a : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
          have b : rk v.val = ry ((runOf p ms).mv t).src := by
            have c : rk v.val = ry v := rfl
            omega
          have b1 := fx_nonneg ((runOf p ms).mv t).src
          have b2 := fx_lt ((runOf p ms).mv t).src
          omega
        have hnokS : ∀ c, ((runOf p ms).pos t).board (toSq ((runOf p ms).mv t).src.val) ≠ some ⟨c, .king⟩ :=
          fun c hh => by rw [toSq_val, hsrc] at hh; cases hh
        have hisKS : (!(cfgOf w b n m).isK (sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val))) = true := by
          rw [hsqD, isK_false_of_noking _ _ hkw hkb hnokS]
          rfl
        have hsrcs : sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val) ∈
            [-1, 1].filterMap (fun df =>
              if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
                some (sqOf (fl v.val + df) (rk v.val)) else none) := by
          refine List.mem_filterMap.mpr ⟨fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst, ?_, ?_⟩
          · rcases hdf with h1' | h1' <;> rw [h1'] <;> decide
          · have hcd : (onb (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val) &&
                !(cfgOf w b n m).isK (sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val))) = true := by
              rw [honbD, hisKS]
              rfl
            show (if onb (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val) &&
                !(cfgOf w b n m).isK (sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val)) then
              some (sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val)) else none) =
              some (sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val))
            rw [if_pos hcd]
        have hsrcs2 : ([-1, 1].filterMap (fun df =>
            if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
              some (sqOf (fl v.val + df) (rk v.val)) else none)).isEmpty = false :=
          List.isEmpty_eq_false_iff.mpr (fun e => by rw [e] at hsrcs; exact List.not_mem_nil hsrcs)
        rw [eprSquares_eq]
        refine ⟨(sqOf (fl v.val) (rk v.val + pdir ((cfgOf w b n m).col t)),
              [-1, 1].filterMap (fun df =>
                if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
                  some (sqOf (fl v.val + df) (rk v.val)) else none)),
            List.mem_filterMap.mpr ⟨v.val, hNKv, ?_⟩⟩
        show (if rk v.val != (if (cfgOf w b n m).col t = 0 then (4 : Int) else 3) then none
          else if (look ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []) (sqOf (fl v.val) (rk v.val + pdir ((cfgOf w b n m).col t)))).isNone then none
          else if ([-1, 1].filterMap (fun df =>
              if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
                some (sqOf (fl v.val + df) (rk v.val)) else none)).isEmpty then none
          else some (v.val, sqOf (fl v.val) (rk v.val + pdir ((cfgOf w b n m).col t)),
            [-1, 1].filterMap (fun df =>
              if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
                some (sqOf (fl v.val + df) (rk v.val)) else none))) =
            some (v.val, sqOf (fl v.val) (rk v.val + pdir ((cfgOf w b n m).col t)),
              [-1, 1].filterMap (fun df =>
                if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
                  some (sqOf (fl v.val + df) (rk v.val)) else none))
        have hrb : (rk v.val != (if (cfgOf w b n m).col t = 0 then (4 : Int) else 3)) = false :=
          bne_eq_false_iff_eq.mpr hrr
        rw [if_neg (fun hh => absurd hh (by rw [hrb]; decide))]
        rw [hgq]
        rw [if_neg (fun hh => absurd hh (by rw [hlkf]; decide))]
        rw [if_neg (fun hh => absurd hh (by rw [hsrcs2]; decide))]

      · have htw : ((runOf p ms).pos t).turn = .black := hturn.trans hcol
        have hrdT : ry ((runOf p ms).mv t).dst = (2 : Int) := hr5.trans (by rw [htw]; decide)
        rw [show ((runOf p ms).pos t).turn.fwd = (-1 : Int) from by rw [htw]; decide] at hry3
        have hsrcR : ry ((runOf p ms).mv t).src = (3 : Int) := by omega
        have hrv : ry v = (3 : Int) := by omega
        have hcolt : (cfgOf w b n m).col t = 1 := hu
        have hrr : rk v.val = (if (cfgOf w b n m).col t = 0 then (4 : Int) else 3) := by
          rw [hcolt, show (if ((1 : Nat) : Nat) = 0 then (4 : Int) else 3) = (3 : Int) from rfl]
          have e : rk v.val = ry v := rfl
          omega
        have hNKv : v.val ∈ (cfgOf w b n m).NK := by
          refine List.mem_filter.mpr ⟨List.mem_range.mpr v.isLt, ?_⟩
          show (!(cfgOf w b n m).isK v.val) = true
          have hnok : ∀ c, ((runOf p ms).pos t).board (toSq v.val) ≠ some ⟨c, .king⟩ :=
            fun c hh => by rw [toSq_val, hvb] at hh; cases hh
          rw [isK_false_of_noking _ _ hkw hkb hnok]
          rfl
        obtain ⟨hE1, -⟩ := roles_eps (g := cfgOf w b n m) t (Nat.le_of_lt ht)
        have hgq : sqOf (fl v.val) (rk v.val + pdir ((cfgOf w b n m).col t)) =
            ((runOf p ms).mv t).dst.val := by
          rw [hcolt, show pdir (1 : Nat) = (-1 : Int) from rfl]
          have h1' : fl v.val = fl ((runOf p ms).mv t).dst.val := by
            have a : fl v.val = fx v := rfl
            have b : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl
            omega
          have h2' : rk v.val + (-1 : Int) = rk ((runOf p ms).mv t).dst.val := by
            have a : rk v.val = ry v := rfl
            have b : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
            omega
          rw [← fl_rk_sqOf (((runOf p ms).mv t).dst.val), h1', h2']
        have hdstNK : ((runOf p ms).mv t).dst.val ∈ (cfgOf w b n m).NK := by
          refine List.mem_filter.mpr ⟨List.mem_range.mpr ((runOf p ms).mv t).dst.isLt, ?_⟩
          show (!(cfgOf w b n m).isK ((runOf p ms).mv t).dst.val) = true
          have hnok : ∀ c, ((runOf p ms).pos t).board (toSq ((runOf p ms).mv t).dst.val) ≠ some ⟨c, .king⟩ :=
            fun c hh => by rw [toSq_val, hdn0] at hh; cases hh
          rw [isK_false_of_noking _ _ hkw hkb hnok]
          rfl
        have honbm : onb (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - (-1 : Int)) = true := by
          simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
          have a : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl
          have b : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
          have b1 := fx_nonneg ((runOf p ms).mv t).dst
          have b2 := fx_lt ((runOf p ms).mv t).dst
          omega
        have honbp : onb (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val + (-1 : Int)) = true := by
          simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
          have a : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl
          have b : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
          have b1 := fx_nonneg ((runOf p ms).mv t).dst
          have b2 := fx_lt ((runOf p ms).mv t).dst
          omega
        obtain ⟨hfox, hroy⟩ := (off_eq_some ((runOf p ms).mv t).dst o 0 ((runOf p ms).pos t).turn.fwd).mp hoo
        rw [show ((runOf p ms).pos t).turn.fwd = (-1 : Int) from by rw [htw]; decide] at hroy
        have hsvm : toSq (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - (-1 : Int))) = v :=
          toSq_sqOf_eq v _ _ honbm (by have a : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl; omega)
            (by have b : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl; omega)
        have hsvp : toSq (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val + (-1 : Int))) = o :=
          toSq_sqOf_eq o _ _ honbp (by have a : fl ((runOf p ms).mv t).dst.val = fx ((runOf p ms).mv t).dst := rfl; omega)
            (by have b : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl; omega)
        have hmemg : ((runOf p ms).mv t).dst.val ∈ epSquares (cfgOf w b n m) t := by
          rw [epSquares_eq]
          refine List.mem_filter.mpr ⟨hdstNK, ?_⟩
          show (rk ((runOf p ms).mv t).dst.val == (if (cfgOf w b n m).col t = 0 then (5 : Int) else 2) &&
            !(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - pdir ((cfgOf w b n m).col t))) &&
            !(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val + pdir ((cfgOf w b n m).col t)))) = true
          rw [hcolt, show pdir (1 : Nat) = (-1 : Int) from rfl, show (if ((1 : Nat) : Nat) = 0 then (5 : Int) else 2) = (2 : Int) from rfl]
          have hc1 : (rk ((runOf p ms).mv t).dst.val == (2 : Int)) = true := by
            apply beq_iff_eq.mpr
            have e : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
            omega
          have hc2 : (!(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - (-1 : Int)))) = true := by
            have hnok : ∀ c, ((runOf p ms).pos t).board (toSq (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val - (-1 : Int)))) ≠ some ⟨c, .king⟩ :=
              fun c hh => by rw [hsvm, hvb] at hh; cases hh
            rw [isK_false_of_noking _ _ hkw hkb hnok]
            rfl
          have hc3 : (!(cfgOf w b n m).isK (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val + (-1 : Int)))) = true := by
            have hnok : ∀ c, ((runOf p ms).pos t).board (toSq (sqOf (fl ((runOf p ms).mv t).dst.val) (rk ((runOf p ms).mv t).dst.val + (-1 : Int)))) ≠ some ⟨c, .king⟩ :=
              fun c hh => by rw [hsvp, hon] at hh; cases hh
            rw [isK_false_of_noking _ _ hkw hkb hnok]
            rfl
          rw [hc1, hc2, hc3]
          rfl
        obtain ⟨kv, hkvE, hkv1⟩ := List.mem_map.mp (show ((runOf p ms).mv t).dst.val ∈
          (((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []).map (·.1)) from hE1 ▸ hmemg)
        have hlkf : (look ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []) ((runOf p ms).mv t).dst.val).isNone = false := by
          show ((((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []).find? (·.1 == ((runOf p ms).mv t).dst.val)).map (·.2)).isNone = false
          cases hfind : ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []).find? (·.1 == ((runOf p ms).mv t).dst.val) with
          | none =>
              exfalso
              rw [List.find?_eq_none] at hfind
              exact hfind kv hkvE (beq_iff_eq.mpr hkv1)
          | some kv' => rfl
        have hdf : fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst = 1 ∨
            fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst = -1 := by omega
        have hF1 : fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst) =
            fl ((runOf p ms).mv t).src.val := by
          have a : fl v.val = fx v := rfl
          have b : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
          omega
        have hR1 : rk v.val = rk ((runOf p ms).mv t).src.val := by
          have a : rk v.val = ry v := rfl
          have b : rk ((runOf p ms).mv t).src.val = ry ((runOf p ms).mv t).src := rfl
          omega
        have hsqD : sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val) =
            ((runOf p ms).mv t).src.val := by
          rw [hF1, hR1, fl_rk_sqOf]
        have honbD : onb (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val) = true := by
          rw [hF1]
          simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
          have a : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
          have b : rk v.val = ry ((runOf p ms).mv t).src := by
            have c : rk v.val = ry v := rfl
            omega
          have b1 := fx_nonneg ((runOf p ms).mv t).src
          have b2 := fx_lt ((runOf p ms).mv t).src
          omega
        have hnokS : ∀ c, ((runOf p ms).pos t).board (toSq ((runOf p ms).mv t).src.val) ≠ some ⟨c, .king⟩ :=
          fun c hh => by rw [toSq_val, hsrc] at hh; cases hh
        have hisKS : (!(cfgOf w b n m).isK (sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val))) = true := by
          rw [hsqD, isK_false_of_noking _ _ hkw hkb hnokS]
          rfl
        have hsrcs : sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val) ∈
            [-1, 1].filterMap (fun df =>
              if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
                some (sqOf (fl v.val + df) (rk v.val)) else none) := by
          refine List.mem_filterMap.mpr ⟨fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst, ?_, ?_⟩
          · rcases hdf with h1' | h1' <;> rw [h1'] <;> decide
          · have hcd : (onb (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val) &&
                !(cfgOf w b n m).isK (sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val))) = true := by
              rw [honbD, hisKS]
              rfl
            show (if onb (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val) &&
                !(cfgOf w b n m).isK (sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val)) then
              some (sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val)) else none) =
              some (sqOf (fl v.val + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk v.val))
            rw [if_pos hcd]
        have hsrcs2 : ([-1, 1].filterMap (fun df =>
            if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
              some (sqOf (fl v.val + df) (rk v.val)) else none)).isEmpty = false :=
          List.isEmpty_eq_false_iff.mpr (fun e => by rw [e] at hsrcs; exact List.not_mem_nil hsrcs)
        rw [eprSquares_eq]
        refine ⟨(sqOf (fl v.val) (rk v.val + pdir ((cfgOf w b n m).col t)),
              [-1, 1].filterMap (fun df =>
                if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
                  some (sqOf (fl v.val + df) (rk v.val)) else none)),
            List.mem_filterMap.mpr ⟨v.val, hNKv, ?_⟩⟩
        show (if rk v.val != (if (cfgOf w b n m).col t = 0 then (4 : Int) else 3) then none
          else if (look ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t []) (sqOf (fl v.val) (rk v.val + pdir ((cfgOf w b n m).col t)))).isNone then none
          else if ([-1, 1].filterMap (fun df =>
              if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
                some (sqOf (fl v.val + df) (rk v.val)) else none)).isEmpty then none
          else some (v.val, sqOf (fl v.val) (rk v.val + pdir ((cfgOf w b n m).col t)),
            [-1, 1].filterMap (fun df =>
              if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
                some (sqOf (fl v.val + df) (rk v.val)) else none))) =
            some (v.val, sqOf (fl v.val) (rk v.val + pdir ((cfgOf w b n m).col t)),
              [-1, 1].filterMap (fun df =>
                if onb (fl v.val + df) (rk v.val) && !(cfgOf w b n m).isK (sqOf (fl v.val + df) (rk v.val)) then
                  some (sqOf (fl v.val + df) (rk v.val)) else none))
        have hrb : (rk v.val != (if (cfgOf w b n m).col t = 0 then (4 : Int) else 3)) = false :=
          bne_eq_false_iff_eq.mpr hrr
        rw [if_neg (fun hh => absurd hh (by rw [hrb]; decide))]
        rw [hgq]
        rw [if_neg (fun hh => absurd hh (by rw [hlkf]; decide))]
        rw [if_neg (fun hh => absurd hh (by rw [hsrcs2]; decide))]


theorem sem_x_val (g : Cfg) (r : Run) (t s k : Nat) :
    (Sem.x t s k).val g r = (code ((r.pos t).board (toSq s)) == k) := rfl

theorem sem_clear_val (g : Cfg) (r : Run) (t : Nat) (ss : List Nat) :
    (Sem.clear t ss).val g r = ss.all fun z => (r.pos t).board (toSq z) == none := rfl

theorem sem_att_val (g : Cfg) (r : Run) (t x s : Nat) :
    (Sem.att t x s).val g r = (match (r.pos t).board (toSq s) with
      | some q => q.color == colorOf (1 - x) &&
          (attacks (r.pos t).board (toSq s) q).contains (toSq (g.K x))
      | none => false) := rfl

theorem sem_att_val_none (g : Cfg) (r : Run) (t x s : Nat)
    (hb : (r.pos t).board (toSq s) = none) : (Sem.att t x s).val g r = false := by
  rw [sem_att_val, hb]

theorem sem_att_val_some (g : Cfg) (r : Run) (t x s : Nat) (q : Piece)
    (hb : (r.pos t).board (toSq s) = some q) :
    (Sem.att t x s).val g r = (q.color == colorOf (1 - x) &&
      (attacks (r.pos t).board (toSq s) q).contains (toSq (g.K x))) := by
  rw [sem_att_val, hb]

theorem core_att_iff_checker (h : ChainAt w b n m p ms) (t x : Nat) (ht : t ≤ n) (hx : x < 2) (s : Nat) :
    (Sem.att t x s).val (cfgOf w b n m) (runOf p ms) = true ↔
      ∃ q, ((runOf p ms).pos t).board (toSq s) = some q ∧ q.color = colorOf (1 - x) ∧
        toSq ((cfgOf w b n m).K x) ∈ attacks ((runOf p ms).pos t).board (toSq s) q := by
  cases hb : ((runOf p ms).pos t).board (toSq s) with
  | none =>
    rw [sem_att_val_none _ _ _ _ _ hb]
    constructor
    · intro h'; exact Bool.noConfusion h'
    · rintro ⟨q, hq, -, -⟩; exact absurd hq.symm (Option.some_ne_none q)
  | some q =>
    rw [sem_att_val_some _ _ _ _ _ _ hb]
    rw [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
    constructor
    · rintro ⟨hc, hm⟩
      exact ⟨q, rfl, hc, hm⟩
    · rintro ⟨q', hq', hc', hm'⟩
      rw [Option.some.injEq] at hq'
      subst hq'
      exact ⟨hc', hm'⟩

theorem eq_of_mem_length_le_one {α : Type} {l : List α} (hlen : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  cases l with
  | nil => simp at ha
  | cons x l =>
    cases l with
    | nil => rw [List.mem_singleton] at ha hb; rw [ha, hb]
    | cons y l => simp only [List.length_cons] at hlen; omega

theorem core_single (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n) (s s' : Nat)
    (hs : (Sem.att t (t % 2) s).val (cfgOf w b n m) (runOf p ms) = true)
    (hs' : (Sem.att t (t % 2) s').val (cfgOf w b n m) (runOf p ms) = true) : toSq s = toSq s' := by
  have hx2 : t % 2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨q, hbq, hcq, hattq⟩ := (core_att_iff_checker h t (t % 2) (Nat.le_of_lt ht) hx2 s).mp hs
  obtain ⟨q', hbq', hcq', hattq'⟩ := (core_att_iff_checker h t (t % 2) (Nat.le_of_lt ht) hx2 s').mp hs'
  have hc0 : C0 ((runOf p ms).pos t) := run_c0 h t (Nat.le_of_lt ht)
  have hturn : ((runOf p ms).pos t).turn = colorOf (t % 2) := run_turn h t (Nat.le_of_lt ht)
  have hrun := run_kings h t (Nat.le_of_lt ht)
  have hstep := run_step h t ht
  have htm : t % 2 = 0 ∨ t % 2 = 1 := by omega
  have hKeq : (cfgOf w b n m).K (t % 2) = if t % 2 = 0 then w.val else b.val := rfl
  have hk : kingAt ((runOf p ms).pos t) ((runOf p ms).pos t).turn (toSq ((cfgOf w b n m).K (t % 2))) := by
    rcases htm with h0 | h1
    · rw [hKeq, if_pos h0, toSq_val, hturn, h0]
      exact hrun.1
    · rw [hKeq, if_neg (by omega : ¬ t % 2 = 0), toSq_val, hturn, h1]
      exact hrun.2.1
  have hopp : ((runOf p ms).pos t).turn.opp = colorOf (1 - t % 2) := by
    rw [hturn]
    rcases htm with h0 | h1
    · rw [h0]
      rfl
    · rw [h1]
      rfl
  have hmem : toSq s ∈ checkers ((runOf p ms).pos t) (toSq ((cfgOf w b n m).K (t % 2))) :=
    (mem_checkers _ _ _).mpr ⟨q, hbq, by rw [hopp]; exact hcq, hattq⟩
  have hmem' : toSq s' ∈ checkers ((runOf p ms).pos t) (toSq ((cfgOf w b n m).K (t % 2))) :=
    (mem_checkers _ _ _).mpr ⟨q', hbq', by rw [hopp]; exact hcq', hattq'⟩
  have hle := checkers_le_one_of_nonking _ _ hc0 hk _ hstep.1 hstep.2.2.1
  exact eq_of_mem_length_le_one hle hmem hmem'

theorem code_eq_emp (b : Option Piece) : (code b == EMP) = (b == none) := by
  cases b with
  | none => rfl
  | some q =>
    obtain ⟨c, k⟩ := q
    cases k <;> cases c <;> rfl

theorem all_take_getD {α : Type} (f : α → Bool) (d : α) : ∀ (l : List α) (j : Nat),
    j + 1 = l.length → l.all f = ((l.take j).all f && f (l.getD j d))
  | [], _, h => absurd h (by simp)
  | [a], 0, _ => by simp
  | [_], _ + 1, h => by simp at h
  | _ :: _ :: _, 0, h => by simp at h
  | a :: b :: l, j + 1, h => by
      have h' : j + 1 = (b :: l).length := by simpa using h
      rw [List.all_cons, List.take_succ_cons, all_take_getD f d (b :: l) j h', List.all_cons,
        Bool.and_assoc, List.getD_cons_succ]

theorem take_one_all {α : Type} (f : α → Bool) (d : α) (l : List α) (h : 1 ≤ l.length) :
    (l.take 1).all f = f (l.getD 0 d) := by
  cases l with
  | nil => simp at h
  | cons a l => simp

theorem core_clear (r : Run) (g : Cfg) (t : Nat) (ss : List Nat) (hss : 2 ≤ ss.length) :
    (Sem.clear t ss).val g r =
      ((((clearLit ss (ss.length - 1)).getD (.x 0 0)).sem t).val g r &&
        (Sem.x t (ss.getD (ss.length - 1) 0) EMP).val g r) := by
  have h1 : ss.length - 1 + 1 = ss.length := by omega
  rw [sem_clear_val, all_take_getD _ 0 ss _ h1, sem_x_val, code_eq_emp]
  congr 1
  · by_cases hj : ss.length - 1 = 1
    · have hcl : clearLit ss (ss.length - 1) = some (.x (ss.getD 0 0) EMP) := by
        rw [clearLit, if_neg (show ¬ ss.length - 1 = 0 by omega), if_pos hj]
      rw [hcl, Option.getD_some,
        show ALit.sem t (.x (ss.getD 0 0) EMP) = Sem.x t (ss.getD 0 0) EMP from rfl, sem_x_val,
        code_eq_emp, hj]
      exact take_one_all _ 0 ss (by omega)
    · have hcl : clearLit ss (ss.length - 1) = some (.clr (ss.take (ss.length - 1))) := by
        rw [clearLit, if_neg (show ¬ ss.length - 1 = 0 by omega), if_neg hj]
      rw [hcl, Option.getD_some,
        show ALit.sem t (.clr (ss.take (ss.length - 1))) = Sem.clear t (ss.take (ss.length - 1)) from rfl,
        sem_clear_val]


theorem colIdx_colorOf (y : Nat) (hy : y < 2) : colIdx (colorOf y) = y := by
  rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> rfl

theorem color_of_colIdx (c : Color) (y : Nat) (h : colIdx c = y) : c = colorOf y := by
  cases c with
  | white =>
    have h0 : colIdx .white = 0 := rfl
    rw [h0] at h
    rw [← h]; rfl
  | black =>
    have h0 : colIdx .black = 1 := rfl
    rw [h0] at h
    rw [← h]; rfl

theorem code_none : code none = 10 := rfl

theorem code_king (c : Color) : code (some ⟨c, .king⟩) = 11 := rfl

theorem code_eq (c : Color) (k : Kind) (hk : k ≠ .king) :
    code (some ⟨c, k⟩) = 5 * colIdx c + kindIdx k := by
  cases k <;> first | rfl | exact absurd rfl hk

theorem code_decode (b : Option Piece) (y pc : Nat) (hy : y < 2) (hpc : pc ≤ 4)
    (h : (code b == 5 * y + pc) = true) :
    ∃ q, b = some q ∧ q.color = colorOf y ∧ kindIdx q.kind = pc := by
  rw [beq_iff_eq] at h
  cases b with
  | none => rw [code_none] at h; omega
  | some q =>
    obtain ⟨c, k⟩ := q
    by_cases hk : k = .king
    · subst hk; rw [code_king] at h; omega
    · rw [code_eq c k hk] at h
      have hb1 : colIdx c ≤ 1 := by cases c <;> decide
      have hb2 : kindIdx k < 5 := by cases k <;> first | decide | exact absurd rfl hk
      have hc : colIdx c = y := by omega
      have hkpc : kindIdx k = pc := by omega
      exact ⟨⟨c, k⟩, rfl, color_of_colIdx c y hc, hkpc⟩

theorem attacksGeom_R (c s k : Nat) (l : List Nat) (hb : between s k = some l)
    (ho : ((fl k - fl s).natAbs == 0 || (rk k - rk s).natAbs == 0) = true) :
    attacksGeom R c s k = true := by
  unfold attacksGeom
  rw [if_neg (show ¬ R = P from by decide), if_neg (show ¬ R = N from by decide), hb, ho]
  rfl

theorem attacksGeom_B (c s k : Nat) (l : List Nat) (hb : between s k = some l)
    (ho : ((fl k - fl s).natAbs == 0 || (rk k - rk s).natAbs == 0) = false) :
    attacksGeom B c s k = true := by
  unfold attacksGeom
  rw [if_neg (show ¬ B = P from by decide), if_neg (show ¬ B = N from by decide), hb, ho]
  rfl

theorem attacksGeom_Q (c s k : Nat) (l : List Nat) (hb : between s k = some l) :
    attacksGeom Q c s k = true := by
  unfold attacksGeom
  rw [if_neg (show ¬ Q = P from by decide), if_neg (show ¬ Q = N from by decide), hb]
  rfl

theorem orth_component_zero (d : Int × Int) (h : d ∈ orth) : d.1 = 0 ∨ d.2 = 0 := by
  simp only [orth, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> rw [h] <;> decide

theorem diag_component_ne (d : Int × Int) (hd : d ∈ orth ++ diag) (h : orth.contains d = false) :
    d.1 ≠ 0 ∧ d.2 ≠ 0 := by
  have hn : d ∉ orth := fun hm => by
    have h2 := List.contains_iff_mem.mpr hm
    rw [h] at h2
    exact Bool.noConfusion h2
  rw [List.mem_append] at hd
  rcases hd with hd | hd
  · exact absurd hd hn
  · simp only [diag, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with h | h | h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

theorem between_ray' (g : Cfg) (x : Nat) (d : Int × Int) (hd : d ∈ orth ++ diag)
    (hK : g.K x < 64) (j : Nat) (hj : j < (g.ray x d).length) (s : Nat)
    (hseq : s = (g.ray x d).getD j 0) :
    ∃ l, between s (g.K x) = some l := by
  subst hseq
  obtain ⟨h64, hf, hr⟩ := ray_getD g x d hd hK j hj
  have hdneg1 : -d.1 = -1 ∨ -d.1 = 0 ∨ -d.1 = 1 := by
    rcases mem_orth_diag_fst d hd with h | h | h <;> rw [h] <;> decide
  have hdneg2 : -d.2 = -1 ∨ -d.2 = 0 ∨ -d.2 = 1 := by
    rcases mem_orth_diag_snd d hd with h | h | h <;> rw [h] <;> decide
  have hdnegne : -d.1 ≠ 0 ∨ -d.2 ≠ 0 := by
    rcases mem_orth_diag_ne d hd with h | h
    · exact Or.inl (fun e => h (by omega))
    · exact Or.inr (fun e => h (by omega))
  have hc : ((↑(j + 1)) : Int) = ↑j + 1 := by omega
  have hf2 : fl (g.K x) = fl ((g.ray x d).getD j 0) + (↑(j + 1)) * (-d.1) := by
    rw [hc, Int.mul_neg, hf]
    omega
  have hr2 : rk (g.K x) = rk ((g.ray x d).getD j 0) + (↑(j + 1)) * (-d.2) := by
    rw [hc, Int.mul_neg, hr]
    omega
  exact ⟨_, between_ray ((g.ray x d).getD j 0) (g.K x) (j + 1) (by omega) (-d.1) (-d.2) hdneg1 hdneg2 hdnegne hf2 hr2⟩

theorem ray_orthLine (g : Cfg) (x : Nat) (d : Int × Int) (hd : d ∈ orth ++ diag)
    (hK : g.K x < 64) (j : Nat) (hj : j < (g.ray x d).length) (s : Nat)
    (hseq : s = (g.ray x d).getD j 0) (horth : d ∈ orth) :
    ((fl (g.K x) - fl s).natAbs == 0 || (rk (g.K x) - rk s).natAbs == 0) = true := by
  obtain ⟨h64, hf, hr⟩ := ray_getD g x d hd hK j hj
  rcases orth_component_zero d horth with hz | hz
  · have hdf : (fl (g.K x) - fl s).natAbs = 0 := by
      rw [hseq, hf, hz, Int.mul_zero, Int.add_zero, Int.sub_self, Int.natAbs_zero]
    rw [hdf, beq_self_eq_true]
    rfl
  · have hdr : (rk (g.K x) - rk s).natAbs = 0 := by
      rw [hseq, hr, hz, Int.mul_zero, Int.add_zero, Int.sub_self, Int.natAbs_zero]
    rw [hdr, beq_self_eq_true, Bool.or_true]

theorem ray_not_orthLine (g : Cfg) (x : Nat) (d : Int × Int) (hd : d ∈ orth ++ diag)
    (hK : g.K x < 64) (j : Nat) (hj : j < (g.ray x d).length) (s : Nat)
    (hseq : s = (g.ray x d).getD j 0) (hdiag : orth.contains d = false) :
    ((fl (g.K x) - fl s).natAbs == 0 || (rk (g.K x) - rk s).natAbs == 0) = false := by
  obtain ⟨h64, hf, hr⟩ := ray_getD g x d hd hK j hj
  obtain ⟨hd1, hd2⟩ := diag_component_ne d hd hdiag
  have hd1' : d.1.natAbs = 1 := by
    rcases mem_orth_diag_fst d hd with h | h | h
    · rw [h]; decide
    · exact absurd h hd1
    · rw [h]; decide
  have hd2' : d.2.natAbs = 1 := by
    rcases mem_orth_diag_snd d hd with h | h | h
    · rw [h]; decide
    · exact absurd h hd2
    · rw [h]; decide
  have hfm : fl (g.K x) - fl s = -((↑j + 1) * d.1) := by rw [hseq, hf]; omega
  have hrm : rk (g.K x) - rk s = -((↑j + 1) * d.2) := by rw [hseq, hr]; omega
  have hdf : (fl (g.K x) - fl s).natAbs ≠ 0 := by
    rw [hfm, Int.natAbs_neg, Int.natAbs_mul, show ((↑j + 1 : Int)).natAbs = j + 1 from by
      rw [show ((↑j + 1 : Int)) = ↑(j + 1) from by omega, Int.natAbs_natCast], hd1']
    omega
  have hdr : (rk (g.K x) - rk s).natAbs ≠ 0 := by
    rw [hrm, Int.natAbs_neg, Int.natAbs_mul, show ((↑j + 1 : Int)).natAbs = j + 1 from by
      rw [show ((↑j + 1 : Int)) = ↑(j + 1) from by omega, Int.natAbs_natCast], hd2']
    omega
  rw [beq_eq_false_iff_ne.mpr hdf, beq_eq_false_iff_ne.mpr hdr]
  rfl

theorem geom_of_ray (g : Cfg) (x : Nat) (d : Int × Int) (hd : d ∈ orth ++ diag)
    (hK : g.K x < 64) (j : Nat) (hj : j < (g.ray x d).length) (s pc : Nat)
    (hseq : s = (g.ray x d).getD j 0) (c : Nat)
    (h : (pc = Q) ∨ (orth.contains d = true ∧ pc = R) ∨ (orth.contains d = false ∧ pc = B)) :
    attacksGeom pc c s (g.K x) = true := by
  obtain ⟨l, hb⟩ := between_ray' g x d hd hK j hj s hseq
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h]; exact attacksGeom_Q c s (g.K x) l hb
  · rw [h2]
    exact attacksGeom_R c s (g.K x) l hb
      (ray_orthLine g x d hd hK j hj s hseq (List.contains_iff_mem.mp h1))
  · rw [h2]
    exact attacksGeom_B c s (g.K x) l hb (ray_not_orthLine g x d hd hK j hj s hseq h1)


theorem mem_take_one {α : Type} {d : α} {l : List α} {z : α} (hz : z ∈ l.take 1) : z = l.getD 0 d := by
  cases l with
  | nil => simp at hz
  | cons a l =>
    rw [List.take_succ_cons, List.take_zero] at hz
    rw [List.getD_cons_zero]
    simpa using hz

theorem getD_zero_mem_take_one {α : Type} (l : List α) (d : α) (h : 1 ≤ l.length) : l.getD 0 d ∈ l.take 1 := by
  cases l with
  | nil => simp at h
  | cons a l =>
    rw [List.take_succ_cons, List.take_zero, List.getD_cons_zero]
    exact List.mem_singleton_self a

theorem clearLit_all_empty (g : Cfg) (r : Run) (t : Nat) (ray : List Nat) (j : Nat)
    (h : ((clearLit ray j).toList).all (fun a => (a.sem t).val g r) = true)
    (z : Nat) (hz : z ∈ ray.take j) : (r.pos t).board (toSq z) = none := by
  cases j with
  | zero => rw [List.take_zero] at hz; simp at hz
  | succ j =>
    cases j with
    | zero =>
      have hcl : clearLit ray 1 = some (.x (ray.getD 0 0) EMP) := by
        rw [clearLit, if_neg (by decide), if_pos rfl]
      rw [hcl, Option.toList_some, List.all_cons, List.all_nil, Bool.and_true] at h
      rw [show ALit.sem t (.x (ray.getD 0 0) EMP) = Sem.x t (ray.getD 0 0) EMP from rfl, sem_x_val] at h
      rw [code_eq_emp] at h
      have hz0 := mem_take_one (d := 0) hz
      rw [hz0]
      exact beq_iff_eq.mp h
    | succ j =>
      have hcl : clearLit ray (j + 2) = some (.clr (ray.take (j + 2))) := by
        rw [clearLit, if_neg (by omega), if_neg (by omega)]
      rw [hcl, Option.toList_some, List.all_cons, List.all_nil, Bool.and_true] at h
      rw [show ALit.sem t (.clr (ray.take (j + 2))) = Sem.clear t (ray.take (j + 2)) from rfl, sem_clear_val,
        List.all_eq_true] at h
      exact beq_iff_eq.mp (h z hz)

theorem clearLit_mk_all (g : Cfg) (r : Run) (t : Nat) (ray : List Nat) (j : Nat)
    (hj : j < ray.length)
    (h : ∀ z ∈ ray.take j, (r.pos t).board (toSq z) = none) :
    ((clearLit ray j).toList).all (fun a => (a.sem t).val g r) = true := by
  rw [List.all_eq_true]
  intro a ha
  cases j with
  | zero =>
    rw [clearLit, if_pos rfl, Option.toList_none] at ha
    simp at ha
  | succ j =>
    cases j with
    | zero =>
      rw [clearLit, if_neg (by decide), if_pos rfl, Option.toList_some, List.mem_singleton] at ha
      subst ha
      rw [show ALit.sem t (.x (ray.getD 0 0) EMP) = Sem.x t (ray.getD 0 0) EMP from rfl, sem_x_val,
        code_eq_emp, beq_iff_eq]
      exact h _ (getD_zero_mem_take_one ray 0 (show 1 ≤ ray.length by omega))
    | succ j =>
      rw [clearLit, if_neg (by omega), if_neg (by omega), Option.toList_some, List.mem_singleton] at ha
      subst ha
      rw [show ALit.sem t (.clr (ray.take (j + 2))) = Sem.clear t (ray.take (j + 2)) from rfl, sem_clear_val,
        List.all_eq_true]
      intro z hz
      rw [h z hz]
      rfl

theorem kindIdx_inj (k k' : Kind) (h : kindIdx k = kindIdx k') : k = k' := by
  cases k <;> cases k' <;> first | rfl | exact absurd h (by decide)

theorem mem_QRB (pc : Nat) (d : Int × Int)
    (hpc : pc ∈ [Q, if orth.contains d then R else B]) :
    (pc = Q) ∨ (orth.contains d = true ∧ pc = R) ∨ (orth.contains d = false ∧ pc = B) := by
  cases hor : orth.contains d with
  | true =>
    rw [hor] at hpc
    have h2 : pc = Q ∨ pc = R := by simpa using hpc
    rcases h2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | false =>
    rw [hor] at hpc
    have h2 : pc = Q ∨ pc = B := by simpa using hpc
    rcases h2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem core_att_sound (h : ChainAt w b n m p ms) (t x : Nat) (ht : t ≤ n) (hx : x < 2) (s : Nat)
    (cs : List (List ALit)) (hcs : (s, cs) ∈ attAlts (cfgOf w b n m) x) (conj : List ALit) (hc : conj ∈ cs)
    (hv : conj.all (fun a => (a.sem t).val (cfgOf w b n m) (runOf p ms)) = true) :
    (Sem.att t x s).val (cfgOf w b n m) (runOf p ms) = true := by
  have hx1 : 1 - x < 2 := by omega
  have hKx : (cfgOf w b n m).K x < 64 := by
    have e : (cfgOf w b n m).K x = if x = 0 then w.val else b.val := rfl
    rw [e]
    by_cases h0 : x = 0
    · rw [if_pos h0]; exact w.isLt
    · rw [if_neg h0]; exact b.isLt
  rw [core_att_iff_checker h t x ht hx s]
  have hm := (mem_attAlts_iff (cfgOf w b n m) x hx s conj).mp ⟨cs, hcs, hc⟩
  rcases hm with ⟨hsNK, hN, hconj⟩ | ⟨hsNK, hP, hconj⟩ | ⟨d, hd, j, hj, hseq, pc, hpc, hconj⟩
  · subst hconj
    rw [List.all_cons, List.all_nil, Bool.and_true] at hv
    rw [show ALit.sem t (.x s (5 * (1 - x) + N)) = Sem.x t s (5 * (1 - x) + N) from rfl, sem_x_val] at hv
    have hs64 : s < 64 := by
      obtain ⟨h1, -⟩ := List.mem_filter.mp hsNK
      exact List.mem_range.mp h1
    obtain ⟨q, hq, hqc, hqk⟩ := code_decode _ (1 - x) N hx1 (by decide) hv
    refine ⟨q, hq, hqc, ?_⟩
    have hqkn : q.kind = .knight := kindIdx_inj _ _ hqk
    rw [mem_attacks_iff]
    refine ⟨?_, ?_⟩
    · have hga : attacksGeom (kindIdx q.kind) (colIdx q.color) (toSq s).val
          (toSq ((cfgOf w b n m).K x)).val = geomAttack q.color q.kind (toSq s) (toSq ((cfgOf w b n m).K x)) :=
        attacksGeom_eq q (by rw [hqkn]; decide) (toSq s) (toSq ((cfgOf w b n m).K x))
      rw [← hga, show (toSq s).val = s from Nat.mod_eq_of_lt hs64,
        show (toSq ((cfgOf w b n m).K x)).val = (cfgOf w b n m).K x from Nat.mod_eq_of_lt hKx, hqk]
      have hqcol : colIdx q.color = 1 - x := by rw [hqc]; exact colIdx_colorOf _ hx1
      rw [hqcol]
      exact hN
    · intro hsl
      rw [hqkn] at hsl
      exact absurd hsl (by decide)
  · subst hconj
    rw [List.all_cons, List.all_nil, Bool.and_true] at hv
    rw [show ALit.sem t (.x s (5 * (1 - x) + P)) = Sem.x t s (5 * (1 - x) + P) from rfl, sem_x_val] at hv
    have hs64 : s < 64 := by
      obtain ⟨h1, -⟩ := List.mem_filter.mp hsNK
      exact List.mem_range.mp h1
    obtain ⟨q, hq, hqc, hqk⟩ := code_decode _ (1 - x) P hx1 (by decide) hv
    refine ⟨q, hq, hqc, ?_⟩
    have hqkn : q.kind = .pawn := kindIdx_inj _ _ hqk
    rw [mem_attacks_iff]
    refine ⟨?_, ?_⟩
    · have hga : attacksGeom (kindIdx q.kind) (colIdx q.color) (toSq s).val
          (toSq ((cfgOf w b n m).K x)).val = geomAttack q.color q.kind (toSq s) (toSq ((cfgOf w b n m).K x)) :=
        attacksGeom_eq q (by rw [hqkn]; decide) (toSq s) (toSq ((cfgOf w b n m).K x))
      rw [← hga, show (toSq s).val = s from Nat.mod_eq_of_lt hs64,
        show (toSq ((cfgOf w b n m).K x)).val = (cfgOf w b n m).K x from Nat.mod_eq_of_lt hKx, hqk]
      have hqcol : colIdx q.color = 1 - x := by rw [hqc]; exact colIdx_colorOf _ hx1
      rw [hqcol]
      exact hP
    · intro hsl
      rw [hqkn] at hsl
      exact absurd hsl (by decide)
  · subst hconj
    rw [List.all_append, Bool.and_eq_true] at hv
    obtain ⟨hcl, hxl⟩ := hv
    rw [List.all_cons, List.all_nil, Bool.and_true] at hxl
    rw [show ALit.sem t (.x s (5 * (1 - x) + pc)) = Sem.x t s (5 * (1 - x) + pc) from rfl, sem_x_val] at hxl
    have hs64 : s < 64 := by
      obtain ⟨h64, -, -⟩ := ray_getD (cfgOf w b n m) x d hd hKx j hj
      rw [hseq]; exact h64
    have h3 := mem_QRB pc d hpc
    have hpc4 : pc ≤ 4 := by
      rcases h3 with h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
    obtain ⟨q, hq, hqc, hqk⟩ := code_decode _ (1 - x) pc hx1 hpc4 hxl
    refine ⟨q, hq, hqc, ?_⟩
    have hqcol : colIdx q.color = 1 - x := by rw [hqc]; exact colIdx_colorOf _ hx1
    have hnok : q.kind ≠ .king := by
      intro e
      rw [e] at hqk
      have e2 : kindIdx .king = 5 := rfl
      rw [e2] at hqk
      omega
    rw [mem_attacks_iff]
    refine ⟨?_, ?_⟩
    · have hga : attacksGeom (kindIdx q.kind) (colIdx q.color) (toSq s).val
          (toSq ((cfgOf w b n m).K x)).val = geomAttack q.color q.kind (toSq s) (toSq ((cfgOf w b n m).K x)) :=
        attacksGeom_eq q hnok (toSq s) (toSq ((cfgOf w b n m).K x))
      rw [← hga, show (toSq s).val = s from Nat.mod_eq_of_lt hs64,
        show (toSq ((cfgOf w b n m).K x)).val = (cfgOf w b n m).K x from Nat.mod_eq_of_lt hKx, hqk, hqcol]
      exact geom_of_ray (cfgOf w b n m) x d hd hKx j hj s pc hseq (1 - x) h3
    · intro hsl z hz
      rw [← toSq_val z]
      apply clearLit_all_empty (cfgOf w b n m) (runOf p ms) t ((cfgOf w b n m).ray x d) j hcl z.val
      have hz2 : inSeg (toSq ((cfgOf w b n m).K x)) (toSq s) z = true := by
        rw [← inSeg_comm]
        exact hz
      have hmb := (mem_btw_iff (toSq ((cfgOf w b n m).K x)) (toSq s) z).mpr hz2
      have hbtw : z.val ∈ btw ((cfgOf w b n m).K x) s := by
        rwa [show (toSq ((cfgOf w b n m).K x)).val = (cfgOf w b n m).K x from Nat.mod_eq_of_lt hKx,
          show (toSq s).val = s from Nat.mod_eq_of_lt hs64] at hmb
      rw [hseq] at hbtw
      rwa [← ray_take_btw (cfgOf w b n m) x d hd hKx j hj] at hbtw


theorem core_att_complete (h : ChainAt w b n m p ms) (t x : Nat) (ht : t ≤ n) (hx : x < 2) (s : Nat)
    (hs : s < 64)
    (ha : (Sem.att t x s).val (cfgOf w b n m) (runOf p ms) = true) :
    ∃ cs, (s, cs) ∈ attAlts (cfgOf w b n m) x ∧
      ∃ conj ∈ cs, conj.all (fun a => (a.sem t).val (cfgOf w b n m) (runOf p ms)) = true := by
  obtain ⟨⟨qc, qk⟩, hq, hqc, hatt⟩ := (core_att_iff_checker h t x ht hx s).mp ha
  rw [mem_attacks_iff] at hatt
  obtain ⟨hgx, hcpx⟩ := hatt
  have hqc' : qc = colorOf (1 - x) := hqc
  have hg' : geomAttack qc qk (toSq s) (toSq ((cfgOf w b n m).K x)) = true := hgx
  have hcp' : isSlider qk = true → clearPath ((runOf p ms).pos t).board (toSq s)
      (toSq ((cfgOf w b n m).K x)) := hcpx
  have hx1 : 1 - x < 2 := by omega
  have hKx : (cfgOf w b n m).K x < 64 := by
    have e : (cfgOf w b n m).K x = if x = 0 then w.val else b.val := rfl
    rw [e]
    by_cases h0 : x = 0
    · rw [if_pos h0]; exact w.isLt
    · rw [if_neg h0]; exact b.isLt
  have hrun := run_kings h t ht
  have htm : x = 0 ∨ x = 1 := by omega
  have hnok : qk ≠ .king := by
    intro e
    subst e
    simp only [geomAttack] at hg'
    rw [beq_iff_eq] at hg'
    have hswb : toSq s = w ∨ toSq s = b := hrun.2.2 (toSq s) qc hq
    have hKwb : toSq ((cfgOf w b n m).K x) = w ∨ toSq ((cfgOf w b n m).K x) = b := by
      rcases htm with h0 | h0
      · rw [h0]
        exact Or.inl (toSq_val w)
      · rw [h0]
        exact Or.inr (toSq_val b)
    rcases hswb with h1 | h1 <;> rcases hKwb with h2 | h2 <;> rw [h1, h2] at hg'
    · have e0 : kdist w w = 0 := by simp [kdist]
      rw [e0] at hg'
      omega
    · have hap := (run_c0 h t ht).apart w b hrun.1 hrun.2.1
      omega
    · rw [kdist_comm] at hg'
      have hap := (run_c0 h t ht).apart w b hrun.1 hrun.2.1
      omega
    · have e0 : kdist b b = 0 := by simp [kdist]
      rw [e0] at hg'
      omega
  have hne_w : s ≠ w.val := by
    intro e
    have e2 : toSq s = w := (congrArg toSq e).trans (toSq_val w)
    rw [e2] at hq
    rw [hrun.1] at hq
    injection hq with e3
    injection e3 with e31 e32
    exact hnok e32.symm
  have hne_b : s ≠ b.val := by
    intro e
    have e2 : toSq s = b := (congrArg toSq e).trans (toSq_val b)
    rw [e2] at hq
    rw [hrun.2.1] at hq
    injection hq with e3
    injection e3 with e31 e32
    exact hnok e32.symm
  have hsNK : s ∈ (cfgOf w b n m).NK := by
    show s ∈ (List.range 64).filter fun s' => !(cfgOf w b n m).isK s'
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hs, by simp [cfgOf, Cfg.isK, hne_w, hne_b]⟩
  have hqcol : colIdx qc = 1 - x := by rw [hqc']; exact colIdx_colorOf _ hx1
  have hAG : attacksGeom (kindIdx qk) (colIdx qc) s ((cfgOf w b n m).K x) = true := by
    have h3 : attacksGeom (kindIdx qk) (colIdx qc) (toSq s).val (toSq ((cfgOf w b n m).K x)).val =
        geomAttack qc qk (toSq s) (toSq ((cfgOf w b n m).K x)) := attacksGeom_eq ⟨qc, qk⟩ hnok _ _
    rw [show (toSq s).val = s from Nat.mod_eq_of_lt hs,
      show (toSq ((cfgOf w b n m).K x)).val = (cfgOf w b n m).K x from Nat.mod_eq_of_lt hKx] at h3
    rw [← h3] at hg'
    exact hg'
  have slider_core (hcp2 : clearPath ((runOf p ms).pos t).board (toSq s) (toSq ((cfgOf w b n m).K x)))
      (halts : aligned (toSq s) (toSq ((cfgOf w b n m).K x)) = true) :
      ∃ d ∈ orth ++ diag, ∃ j, j < ((cfgOf w b n m).ray x d).length ∧
        s = ((cfgOf w b n m).ray x d).getD j 0 := by
    have halt : aligned (toSq ((cfgOf w b n m).K x)) (toSq s) = true := by
      rw [← aligned_comm]; exact halts
    have hKob : ∃ c, ((runOf p ms).pos t).board (toSq ((cfgOf w b n m).K (1 - x))) = some ⟨c, .king⟩ := by
      have hKo1 : (cfgOf w b n m).K (1 - x) = if x = 0 then b.val else w.val := by
        rcases htm with h0 | h0
        · rw [h0]
          rfl
        · rw [h0]
          rfl
      rw [hKo1]
      rcases htm with h0 | h0
      · rw [if_pos h0, toSq_val]; exact ⟨.black, hrun.2.1⟩
      · rw [if_neg (by omega), toSq_val]; exact ⟨.white, hrun.1⟩
    have hs'ne : toSq s ≠ toSq ((cfgOf w b n m).K (1 - x)) := by
      intro e
      obtain ⟨c', hkb⟩ := hKob
      rw [← e] at hkb
      rw [hq] at hkb
      injection hkb with e3
      injection e3 with e31 e32
      exact hnok e32
    have hinSeg0 : inSeg (toSq ((cfgOf w b n m).K x)) (toSq s) (toSq ((cfgOf w b n m).K (1 - x))) = false := by
      cases hc0 : inSeg (toSq ((cfgOf w b n m).K x)) (toSq s) (toSq ((cfgOf w b n m).K (1 - x))) with
      | false => rfl
      | true =>
        rw [inSeg_comm] at hc0
        have hn := hcp2 _ hc0
        obtain ⟨c', hkb⟩ := hKob
        rw [hkb] at hn
        exact absurd hn (Option.some_ne_none _)
    have hapart : 2 ≤ kdist (toSq (cfgOf w b n m).kw) (toSq (cfgOf w b n m).kb) := by
      have h2 := (run_c0 h t ht).apart w b hrun.1 hrun.2.1
      rwa [show (cfgOf w b n m).kw = w.val from rfl, show (cfgOf w b n m).kb = b.val from rfl,
        toSq_val, toSq_val]
    have hmrs : (toSq s).val ∈ (cfgOf w b n m).raySquares x :=
      (mem_raySquares_iff (cfgOf w b n m) w.isLt b.isLt hapart x hx (toSq s)).mpr ⟨halt, hs'ne, hinSeg0⟩
    have hmrs2 : s ∈ (cfgOf w b n m).raySquares x := by
      have e : (toSq s).val = s := Nat.mod_eq_of_lt hs
      rwa [e] at hmrs
    rw [raySquares_eq, List.mem_flatMap] at hmrs2
    obtain ⟨d, hd, hsd⟩ := hmrs2
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hsd
    have hseq : s = ((cfgOf w b n m).ray x d).getD j 0 := by
      rw [← hjv]
      rw [List.getElem_eq_getD]
    exact ⟨d, hd, j, hj, hseq⟩
  have sq_clear (hcp2 : clearPath ((runOf p ms).pos t).board (toSq s) (toSq ((cfgOf w b n m).K x)))
      (d : Int × Int) (hd : d ∈ orth ++ diag) (j : Nat)
      (hj : j < ((cfgOf w b n m).ray x d).length) (hseq : s = ((cfgOf w b n m).ray x d).getD j 0)
      (z : Nat) (hz : z ∈ ((cfgOf w b n m).ray x d).take j) :
      ((runOf p ms).pos t).board (toSq z) = none := by
    have hz64 : z < 64 := by
      have hz2 : z ∈ (cfgOf w b n m).ray x d := List.mem_of_mem_take hz
      rw [List.mem_iff_getElem] at hz2
      obtain ⟨i, hi, hiz⟩ := hz2
      obtain ⟨h64i, -, -⟩ := ray_getD (cfgOf w b n m) x d hd hKx i hi
      rw [← hiz, List.getElem_eq_getD]
      exact h64i
    have hbtw : z ∈ btw ((cfgOf w b n m).K x) s := by
      have h1 := hz
      rw [ray_take_btw (cfgOf w b n m) x d hd hKx j hj, ← hseq] at h1
      exact h1
    have hiS : inSeg (toSq s) (toSq ((cfgOf w b n m).K x)) (toSq z) = true := by
      have hmb := (mem_btw_iff (toSq ((cfgOf w b n m).K x)) (toSq s) (toSq z)).mp (by
        rwa [show (toSq ((cfgOf w b n m).K x)).val = (cfgOf w b n m).K x from Nat.mod_eq_of_lt hKx,
          show (toSq s).val = s from Nat.mod_eq_of_lt hs,
          show (toSq z).val = z from Nat.mod_eq_of_lt hz64])
      rw [inSeg_comm] at hmb
      exact hmb
    exact hcp2 _ hiS
  cases hk : qk with
  | king => exact absurd hk hnok
  | knight =>
    have hN : attacksGeom N (1 - x) s ((cfgOf w b n m).K x) = true := by
      rw [hk, hqcol] at hAG
      exact hAG
    obtain ⟨cs', hcs', hcm⟩ :=
      (mem_attAlts_iff (cfgOf w b n m) x hx s [.x s (5 * (1 - x) + N)]).mpr (Or.inl ⟨hsNK, hN, rfl⟩)
    refine ⟨cs', hcs', _, hcm, ?_⟩
    rw [List.all_cons, List.all_nil, Bool.and_true,
      show ALit.sem t (.x s (5 * (1 - x) + N)) = Sem.x t s (5 * (1 - x) + N) from rfl, sem_x_val, hq,
      code_eq qc qk hnok, hqcol, hk]
    exact beq_self_eq_true _
  | pawn =>
    have hP : attacksGeom P (1 - x) s ((cfgOf w b n m).K x) = true := by
      rw [hk, hqcol] at hAG
      exact hAG
    obtain ⟨cs', hcs', hcm⟩ :=
      (mem_attAlts_iff (cfgOf w b n m) x hx s [.x s (5 * (1 - x) + P)]).mpr (Or.inr (Or.inl ⟨hsNK, hP, rfl⟩))
    refine ⟨cs', hcs', _, hcm, ?_⟩
    rw [List.all_cons, List.all_nil, Bool.and_true,
      show ALit.sem t (.x s (5 * (1 - x) + P)) = Sem.x t s (5 * (1 - x) + P) from rfl, sem_x_val, hq,
      code_eq qc qk hnok, hqcol, hk]
    exact beq_self_eq_true _
  | bishop =>
    have hd2 : diagLine (toSq s) (toSq ((cfgOf w b n m).K x)) = true := by
      have hh := hg'
      rw [hk] at hh
      exact hh
    rw [diagLine, Bool.and_eq_true] at hd2
    obtain ⟨hal, hnot⟩ := hd2
    have hfne : fx (toSq s) ≠ fx (toSq ((cfgOf w b n m).K x)) := by
      intro e
      have h1 : (fx (toSq s) == fx (toSq ((cfgOf w b n m).K x))) = true := beq_iff_eq.mpr e
      have h2 : (fx (toSq s) == fx (toSq ((cfgOf w b n m).K x)) ||
          ry (toSq s) == ry (toSq ((cfgOf w b n m).K x))) = true := by rw [h1]; rfl
      rw [h2] at hnot
      exact absurd hnot (by decide)
    have hrne : ry (toSq s) ≠ ry (toSq ((cfgOf w b n m).K x)) := by
      intro e
      have h1 : (ry (toSq s) == ry (toSq ((cfgOf w b n m).K x))) = true := beq_iff_eq.mpr e
      have h2 : (fx (toSq s) == fx (toSq ((cfgOf w b n m).K x)) ||
          ry (toSq s) == ry (toSq ((cfgOf w b n m).K x))) = true := by rw [h1, Bool.or_true]
      rw [h2] at hnot
      exact absurd hnot (by decide)
    have hcp2 : clearPath ((runOf p ms).pos t).board (toSq s) (toSq ((cfgOf w b n m).K x)) :=
      hcp' (by rw [hk]; decide)
    obtain ⟨d, hd, j, hj, hseq⟩ := slider_core hcp2 hal
    obtain ⟨h64', hf, hr⟩ := ray_getD (cfgOf w b n m) x d hd hKx j hj
    rw [← hseq] at hf hr
    have horF : orth.contains d = false := by
      cases hcc : orth.contains d with
      | false => rfl
      | true =>
        exfalso
        obtain hz1 | hz2 := orth_component_zero d (List.contains_iff_mem.mp hcc)
        · apply hfne
          rw [fx_toSq s hs, fx_toSq _ hKx, hf, hz1, Int.mul_zero, Int.add_zero]
        · apply hrne
          rw [ry_toSq s hs, ry_toSq _ hKx, hr, hz2, Int.mul_zero, Int.add_zero]
    have hpcB : B ∈ [Q, if orth.contains d then R else B] := by
      rw [horF]
      decide
    obtain ⟨cs', hcs', hcm⟩ := (mem_attAlts_iff (cfgOf w b n m) x hx s
      ((clearLit ((cfgOf w b n m).ray x d) j).toList ++
        [.x s (5 * (1 - x) + B)])).mpr
      (Or.inr (Or.inr ⟨d, hd, j, hj, hseq, B, hpcB, rfl⟩))
    refine ⟨cs', hcs', _, hcm, ?_⟩
    rw [List.all_append, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · exact clearLit_mk_all (cfgOf w b n m) (runOf p ms) t ((cfgOf w b n m).ray x d) j hj
        (sq_clear hcp2 d hd j hj hseq)
    · rw [List.all_cons, List.all_nil, Bool.and_true,
        show ALit.sem t (.x s (5 * (1 - x) + B)) =
          Sem.x t s (5 * (1 - x) + B) from rfl, sem_x_val, hq,
        code_eq qc qk hnok, hqcol, hk]
      exact beq_self_eq_true _
  | rook =>
    have hor : orthLine (toSq s) (toSq ((cfgOf w b n m).K x)) = true := by
      have hh := hg'
      rw [hk] at hh
      exact hh
    simp only [orthLine, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hor
    obtain ⟨hal, hoo⟩ := hor
    have hcp2 : clearPath ((runOf p ms).pos t).board (toSq s) (toSq ((cfgOf w b n m).K x)) :=
      hcp' (by rw [hk]; decide)
    obtain ⟨d, hd, j, hj, hseq⟩ := slider_core hcp2 hal
    obtain ⟨h64', hf, hr⟩ := ray_getD (cfgOf w b n m) x d hd hKx j hj
    rw [← hseq] at hf hr
    have horT : orth.contains d = true := by
      rw [List.contains_iff_mem]
      rcases hoo with hfx | hry
      · rw [fx_toSq s hs, fx_toSq _ hKx] at hfx
        rcases Int.mul_eq_zero.mp (show (↑j + 1) * d.1 = 0 by omega) with h0 | h0
        · omega
        · rcases mem_orth_diag_snd d hd with h1 | h1 | h1
          · have e : d = (0, -1) := Prod.ext (y := ((0 : Int), (-1 : Int))) h0 h1
            rw [e]; decide
          · rcases mem_orth_diag_ne d hd with hn | hn
            · exact absurd h0 hn
            · exact absurd h1 hn
          · have e : d = (0, 1) := Prod.ext (y := ((0 : Int), (1 : Int))) h0 h1
            rw [e]; decide
      · rw [ry_toSq s hs, ry_toSq _ hKx] at hry
        rcases Int.mul_eq_zero.mp (show (↑j + 1) * d.2 = 0 by omega) with h0 | h0
        · omega
        · rcases mem_orth_diag_fst d hd with h1 | h1 | h1
          · have e : d = (-1, 0) := Prod.ext (y := ((-1 : Int), (0 : Int))) h1 h0
            rw [e]; decide
          · rcases mem_orth_diag_ne d hd with hn | hn
            · exact absurd h1 hn
            · exact absurd h0 hn
          · have e : d = (1, 0) := Prod.ext (y := ((1 : Int), (0 : Int))) h1 h0
            rw [e]; decide
    have hpcR : R ∈ [Q, if orth.contains d then R else B] := by
      rw [horT]
      decide
    obtain ⟨cs', hcs', hcm⟩ := (mem_attAlts_iff (cfgOf w b n m) x hx s
      ((clearLit ((cfgOf w b n m).ray x d) j).toList ++
        [.x s (5 * (1 - x) + R)])).mpr
      (Or.inr (Or.inr ⟨d, hd, j, hj, hseq, R, hpcR, rfl⟩))
    refine ⟨cs', hcs', _, hcm, ?_⟩
    rw [List.all_append, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · exact clearLit_mk_all (cfgOf w b n m) (runOf p ms) t ((cfgOf w b n m).ray x d) j hj
        (sq_clear hcp2 d hd j hj hseq)
    · rw [List.all_cons, List.all_nil, Bool.and_true,
        show ALit.sem t (.x s (5 * (1 - x) + R)) =
          Sem.x t s (5 * (1 - x) + R) from rfl, sem_x_val, hq,
        code_eq qc qk hnok, hqcol, hk]
      exact beq_self_eq_true _
  | queen =>
    have hal : aligned (toSq s) (toSq ((cfgOf w b n m).K x)) = true := by
      have hh := hg'
      rw [hk] at hh
      exact hh
    have hcp2 : clearPath ((runOf p ms).pos t).board (toSq s) (toSq ((cfgOf w b n m).K x)) :=
      hcp' (by rw [hk]; decide)
    obtain ⟨d, hd, j, hj, hseq⟩ := slider_core hcp2 hal
    have hpcQ : Q ∈ [Q, if orth.contains d then R else B] := List.mem_cons_self
    obtain ⟨cs', hcs', hcm⟩ := (mem_attAlts_iff (cfgOf w b n m) x hx s
      ((clearLit ((cfgOf w b n m).ray x d) j).toList ++
        [.x s (5 * (1 - x) + Q)])).mpr
      (Or.inr (Or.inr ⟨d, hd, j, hj, hseq, Q, hpcQ, rfl⟩))
    refine ⟨cs', hcs', _, hcm, ?_⟩
    rw [List.all_append, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · exact clearLit_mk_all (cfgOf w b n m) (runOf p ms) t ((cfgOf w b n m).ray x d) j hj
        (sq_clear hcp2 d hd j hj hseq)
    · rw [List.all_cons, List.all_nil, Bool.and_true,
        show ALit.sem t (.x s (5 * (1 - x) + Q)) =
          Sem.x t s (5 * (1 - x) + Q) from rfl, sem_x_val, hq,
        code_eq qc qk hnok, hqcol, hk]
      exact beq_self_eq_true _

theorem colorOf_opp1 (x : Nat) (hx : x < 2) : (colorOf x).opp = colorOf (1 - x) := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rfl

theorem colorOf_opp2 (x : Nat) (hx : x < 2) : (colorOf (1 - x)).opp = colorOf x := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rfl

theorem colorOf_colIdx (x : Nat) (hx : x < 2) : colIdx (colorOf x) = x := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rfl

theorem cfg_K_lt (w b : Sq) (n m x : Nat) (hx : x < 2) : (cfgOf w b n m).K x < 64 := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
  · exact w.isLt
  · exact b.isLt

theorem cfg_K_toval (w b : Sq) (n m x : Nat) (hx : x < 2) :
    (toSq ((cfgOf w b n m).K x)).val = (cfgOf w b n m).K x :=
  Nat.mod_eq_of_lt (cfg_K_lt w b n m x hx)

theorem run_kingAt' (h : ChainAt w b n m p ms) (t : Nat) (ht : t ≤ n) (x : Nat) (hx : x < 2) :
    kingAt ((runOf p ms).pos t) (colorOf x) (toSq ((cfgOf w b n m).K x)) := by
  obtain ⟨hw, hb, -⟩ := run_kings h t ht
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
  · show kingAt ((runOf p ms).pos t) .white (toSq w.val)
    rw [toSq_val]; exact hw
  · show kingAt ((runOf p ms).pos t) .black (toSq b.val)
    rw [toSq_val]; exact hb

theorem run_king_uniq' (h : ChainAt w b n m p ms) (t : Nat) (ht : t ≤ n) (x : Nat) (hx : x< 2)
    (s : Sq) (hs : kingAt ((runOf p ms).pos t) (colorOf x) s) :
    s = toSq ((cfgOf w b n m).K x) := by
  obtain ⟨hw, hb, hu⟩ := run_kings h t ht
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
  · rcases hu s .white hs with e | e
    · rw [e]; exact (toSq_val w).symm
    · exfalso
      rw [e] at hs
      exact absurd (congrArg Piece.color (Option.some.inj (hs.symm.trans hb))) (by decide)
  · rcases hu s .black hs with e | e
    · exfalso
      rw [e] at hs
      exact absurd (congrArg Piece.color (Option.some.inj (hs.symm.trans hw))) (by decide)
    · rw [e]; exact (toSq_val b).symm

theorem run_apart' (h : ChainAt w b n m p ms) : 2 ≤ kdist w b :=
  (run_c0 h 0 (Nat.zero_le n)).apart w b (run_kings h 0 (Nat.zero_le n)).1 (run_kings h 0 (Nat.zero_le n)).2.1

theorem run_neK' (h : ChainAt w b n m p ms) (t : Nat) (ht : t ≤ n) (s : Sq) (q : Piece)
    (hq : ((runOf p ms).pos t).board s = some q) (hk : q.kind ≠ .king) : s ≠ w ∧ s ≠ b := by
  obtain ⟨hw, hb, -⟩ := run_kings h t ht
  constructor
  · intro e
    rw [e] at hq
    exact hk (congrArg Piece.kind (Option.some.inj (hq.symm.trans hw)))
  · intro e
    rw [e] at hq
    exact hk (congrArg Piece.kind (Option.some.inj (hq.symm.trans hb)))

theorem not_isK_of_ne (w b : Sq) (n m : Nat) (s : Sq) (hsw : s ≠ w) (hsb : s ≠ b) :
    (cfgOf w b n m).isK s.val = false := by
  have h1 : (s.val == w.val) = false := beq_eq_false_iff_ne.mpr fun e => hsw (Fin.ext e)
  have h2 : (s.val == b.val) = false := beq_eq_false_iff_ne.mpr fun e => hsb (Fin.ext e)
  show (s.val == w.val || s.val == b.val) = false
  rw [h1, h2]
  rfl

theorem run_inCheck' (h : ChainAt w b n m p ms) (t : Nat) (h1 : 1 ≤ t) (ht : t < n) :
    inCheck ((runOf p ms).pos t) (colorOf (t % 2)) = true := by
  obtain ⟨-, hgc, -, hstep⟩ := run_step h (t - 1) (by omega)
  have h2 := lemmaE_inCheck _ _ hgc
  rw [← hstep, Nat.sub_add_cancel h1, run_turn h t (Nat.le_of_lt ht)] at h2
  exact h2

theorem attacks_inSeg_slider (B : Board) (S KK z : Sq) (q : Piece) (hkk : q.kind ≠ .king)
    (hatt : KK ∈ attacks B S q) (hz : inSeg S KK z = true) :
    isSlider q.kind = true ∧ clearPath B S KK := by
  obtain ⟨hg, hcl⟩ := (mem_attacks_iff B S KK q).mp hatt
  have hnz := inSeg_ne hz
  have hkd : 2 ≤ kdist S KK := by
    have h1 := (inSeg_aligned S KK z hz).2.2
    have h2 := kdist_pos S z (Ne.symm hnz.1)
    omega
  have hsl : isSlider q.kind = true := by
    obtain ⟨c, kd⟩ := q
    cases kd with
    | pawn =>
      exfalso
      simp only [geomAttack, Bool.and_eq_true, beq_iff_eq] at hg
      cases c <;> simp only [Color.fwd] at hg
      · have h3 : kdist S KK = 1 := by simp only [kdist]; omega
        omega
      · have h3 : kdist S KK = 1 := by simp only [kdist]; omega
        omega
    | knight =>
      exfalso
      have hna := knightJump_not_aligned S KK hg
      rw [aligned_ab_of_inSeg hz] at hna
      exact absurd hna (by decide)
    | king => exact absurd rfl hkk
    | bishop => rfl
    | rook => rfl
    | queen => rfl
  exact ⟨hsl, hcl hsl⟩

theorem cand_geom_of (w b : Sq) (n m x : Nat) (hx : x < 2) (s : Sq) (q : Piece)
    (hk : q.kind ≠ .king) (hkn : q.kind = .knight ∨ q.kind = .pawn)
    (hcol : colIdx q.color = 1 - x)
    (hg : geomAttack q.color q.kind s (toSq ((cfgOf w b n m).K x)) = true)
    (hsw : s ≠ w) (hsb : s ≠ b) :
    (cfgOf w b n m).cand x s.val = true := by
  have hnot := not_isK_of_ne w b n m s hsw hsb
  have hKv := cfg_K_toval w b n m x hx
  have e := (attacksGeom_eq q hk s (toSq ((cfgOf w b n m).K x))).trans hg
  rw [hcol, hKv] at e
  simp only [Cfg.cand, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  refine Or.inr ⟨hnot, ?_⟩
  rcases hkn with hk1 | hk1
  · rw [hk1] at e; exact Or.inl e
  · rw [hk1] at e; exact Or.inr e

theorem cand_ray_of (w b : Sq) (n m : Nat) (hap : 2 ≤ kdist w b) (x : Nat) (hx : x < 2) (s : Sq)
    (hal : aligned (toSq ((cfgOf w b n m).K x)) s = true)
    (hsk : s ≠ toSq ((cfgOf w b n m).K (1 - x)))
    (hins : inSeg (toSq ((cfgOf w b n m).K x)) s (toSq ((cfgOf w b n m).K (1 - x))) = false) :
    (cfgOf w b n m).cand x s.val = true := by
  have hkk : 2 ≤ kdist (toSq (cfgOf w b n m).kw) (toSq (cfgOf w b n m).kb) := by
    show 2 ≤ kdist (toSq w.val) (toSq b.val)
    rw [toSq_val, toSq_val]; exact hap
  have hmem := (mem_raySquares_iff (cfgOf w b n m) w.isLt b.isLt hkk x (by omega) s).mpr
    ⟨hal, hsk, hins⟩
  simp only [Cfg.cand, Bool.or_eq_true]
  exact Or.inl (List.contains_iff_mem.mpr hmem)

theorem raySquares_mem_of (w b : Sq) (n m x : Nat) (hx : x < 2) (hap : 2 ≤ kdist w b) (z : Sq)
    (hal : aligned (toSq ((cfgOf w b n m).K x)) z = true)
    (hne : z ≠ toSq ((cfgOf w b n m).K (1 - x)))
    (hins : inSeg (toSq ((cfgOf w b n m).K x)) z (toSq ((cfgOf w b n m).K (1 - x))) = false) :
    ((cfgOf w b n m).raySquares x).contains z.val = true := by
  have hkk : 2 ≤ kdist (toSq (cfgOf w b n m).kw) (toSq (cfgOf w b n m).kb) := by
    show 2 ≤ kdist (toSq w.val) (toSq b.val)
    rw [toSq_val, toSq_val]; exact hap
  exact List.contains_iff_mem.mpr
    ((mem_raySquares_iff (cfgOf w b n m) w.isLt b.isLt hkk x (by omega) z).mpr ⟨hal, hne, hins⟩)

theorem core_r1 (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n) (q : Sq) (pc : Piece)
    (hq : ((runOf p ms).pos (t + 1)).board q = some pc) (hc : pc.color = colorOf (t % 2))
    (ha : toSq ((cfgOf w b n m).K (1 - t % 2)) ∈ attacks ((runOf p ms).pos (t + 1)).board q pc) :
    q = ((runOf p ms).mv t).dst ∨
      ∃ z, inSeg q (toSq ((cfgOf w b n m).K (1 - t % 2))) z = true ∧
        (z = ((runOf p ms).mv t).src ∨ epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some z) := by
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step h t ht
  by_cases hdst : q = ((runOf p ms).mv t).dst
  · exact Or.inl hdst
  · right
    have hle : t ≤ n := Nat.le_of_lt ht
    have hlt2 : t % 2 < 2 := Nat.mod_lt t (by decide)
    have hsd : ((runOf p ms).mv t).src ≠ ((runOf p ms).mv t).dst := legal_src_ne_dst _ _ hleg
    have hsrc : q ≠ ((runOf p ms).mv t).src := by
      intro e
      have h1 : ((runOf p ms).pos (t + 1)).board ((runOf p ms).mv t).src = none := by
        rw [hstep]; exact play_board_src _ _ hsd
      rw [← e, hq] at h1
      simp at h1
    have hevq : epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) ≠ some q := by
      intro he
      have h1 : ((runOf p ms).pos (t + 1)).board q = none := by
        rw [hstep]; exact play_board_epVictim _ _ q he hdst
      rw [hq] at h1
      simp at h1
    have hqt : ((runOf p ms).pos t).board q = some pc := by
      have e := nonking_board_change _ _ hleg hkm q hsrc hdst hevq
      rw [← hstep] at e
      rw [← e]; exact hq
    have hsafe0 := (run_c0 h t hle).safe
    rw [run_turn h t hle, colorOf_opp1 (t % 2) hlt2] at hsafe0
    have hKk : kingAt ((runOf p ms).pos t) (colorOf (1 - t % 2))
        (toSq ((cfgOf w b n m).K (1 - t % 2))) := run_kingAt' h t hle (1 - t % 2) (by omega)
    have hnoatt : toSq ((cfgOf w b n m).K (1 - t % 2)) ∉
        attacks ((runOf p ms).pos t).board q pc := by
      intro hmem
      have hatt : attacked ((runOf p ms).pos t).board (toSq ((cfgOf w b n m).K (1 - t % 2)))
          (colorOf (1 - t % 2)).opp = true := by
        rw [colorOf_opp2 (t % 2) hlt2]
        exact (attacked_iff _ _ _).mpr ⟨q, pc, hqt, hc, hmem⟩
      have hic : inCheck ((runOf p ms).pos t) (colorOf (1 - t % 2)) = true :=
        (inCheck_iff _ _).mpr ⟨_, hKk, hatt⟩
      rw [hic] at hsafe0
      exact absurd hsafe0 (by decide)
    obtain ⟨hg1, hcl1⟩ := (mem_attacks_iff _ _ _ _).mp ha
    cases hsl : isSlider pc.kind with
    | false =>
      exact absurd ((mem_attacks_iff _ _ _ _).mpr ⟨hg1, fun hh => by
        rw [hh] at hsl; exact absurd hsl (by decide)⟩) hnoatt
    | true =>
      have hncp : ¬ clearPath ((runOf p ms).pos t).board q
          (toSq ((cfgOf w b n m).K (1 - t % 2))) := fun hcp =>
        hnoatt ((mem_attacks_iff _ _ _ _).mpr ⟨hg1, fun _ => hcp⟩)
      obtain ⟨z, hz⟩ := Classical.not_forall.mp hncp
      obtain ⟨hzseg, hznone⟩ := Classical.not_imp.mp hz
      have hz1 : ((runOf p ms).pos (t + 1)).board z = none := hcl1 hsl z hzseg
      have hzd : z ≠ ((runOf p ms).mv t).dst := by
        obtain ⟨q0, hq0, -, -⟩ := legal_nonking_mem _ _ hleg hkm
        intro e
        have hbn : ((runOf p ms).pos (t + 1)).board ((runOf p ms).mv t).dst ≠ none := by
          rw [hstep, play_board_dst, hq0]
          cases hpr : ((runOf p ms).mv t).promo with
          | none => intro hh; simp at hh
          | some k0 => intro hh; simp at hh
        rw [e] at hz1
        exact hbn hz1
      by_cases hzsrc : z = ((runOf p ms).mv t).src
      · exact ⟨z, hzseg, Or.inl hzsrc⟩
      · by_cases hzep : epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some z
        · exact ⟨z, hzseg, Or.inr hzep⟩
        · exfalso
          have hch := nonking_board_change _ _ hleg hkm z hzsrc hzd hzep
          rw [← hstep] at hch
          rw [hz1] at hch
          exact hznone hch.symm

theorem core_r2 (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n) (q : Sq) (pc : Piece)
    (hq : ((runOf p ms).pos t).board q = some pc) (hc : pc.color = colorOf (1 - t % 2))
    (ha : toSq ((cfgOf w b n m).K (t % 2)) ∈ attacks ((runOf p ms).pos t).board q pc) :
    ((runOf p ms).mv t).dst = q ∨ epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some q ∨
      inSeg q (toSq ((cfgOf w b n m).K (t % 2))) ((runOf p ms).mv t).dst = true := by
  obtain ⟨hleg, -, hkm, -⟩ := run_step h t ht
  have hle : t ≤ n := Nat.le_of_lt ht
  have hlt2 : t % 2 < 2 := Nat.mod_lt t (by decide)
  have hk : kingAt ((runOf p ms).pos t) ((runOf p ms).pos t).turn
      (toSq ((cfgOf w b n m).K (t % 2))) := by
    rw [run_turn h t hle]; exact run_kingAt' h t hle (t % 2) hlt2
  have hcc : pc.color = ((runOf p ms).pos t).turn.opp := by
    rw [hc, run_turn h t hle, colorOf_opp1 (t % 2) hlt2]
  have hcq : q ∈ checkers ((runOf p ms).pos t) (toSq ((cfgOf w b n m).K (t % 2))) :=
    (mem_checkers _ _ _).mpr ⟨pc, hq, hcc, ha⟩
  exact checker_removed_or_blocked _ _ _ (run_c0 h t hle) hk hcq _ hleg hkm

theorem core_r3 (h : ChainAt w b n m p ms) (t : Nat) (h1 : 1 ≤ t) (ht : t < n) :
    (cfgOf w b n m).cand (t % 2) ((runOf p ms).mv t).dst.val = true ∨
      ∃ v, epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some v ∧
        (cfgOf w b n m).cand (t % 2) v.val = true := by
  obtain ⟨hleg, -, hkm, -⟩ := run_step h t ht
  have hle : t ≤ n := Nat.le_of_lt ht
  have hlt2 : t % 2 < 2 := Nat.mod_lt t (by decide)
  have hc0 := run_c0 h t hle
  have hkk : kingAt ((runOf p ms).pos t) ((runOf p ms).pos t).turn
      (toSq ((cfgOf w b n m).K (t % 2))) := by
    rw [run_turn h t hle]; exact run_kingAt' h t hle (t % 2) hlt2
  have huniq : ∀ s, kingAt ((runOf p ms).pos t) ((runOf p ms).pos t).turn s →
      s = toSq ((cfgOf w b n m).K (t % 2)) := by
    intro s hs
    rw [run_turn h t hle] at hs
    exact run_king_uniq' h t hle (t % 2) hlt2 s hs
  have hic : inCheck ((runOf p ms).pos t) ((runOf p ms).pos t).turn = true := by
    rw [run_turn h t hle]; exact run_inCheck' h t h1 ht
  have hne : checkers ((runOf p ms).pos t) (toSq ((cfgOf w b n m).K (t % 2))) ≠ [] :=
    (inCheck_iff_checkers _ _ hkk huniq).mp hic
  have hle1 := checkers_le_one_of_nonking _ _ hc0 hkk _ hleg hkm
  obtain ⟨c, hcl⟩ : ∃ c, checkers ((runOf p ms).pos t) (toSq ((cfgOf w b n m).K (t % 2))) = [c] := by
    cases hcl : checkers ((runOf p ms).pos t) (toSq ((cfgOf w b n m).K (t % 2))) with
    | nil => exact absurd hcl hne
    | cons c rest =>
      cases rest with
      | nil => exact ⟨c, rfl⟩
      | cons d rest2 =>
        rw [hcl] at hle1
        simp only [List.length_cons] at hle1
        omega
  have hcm : c ∈ checkers ((runOf p ms).pos t) (toSq ((cfgOf w b n m).K (t % 2))) := by
    rw [hcl]; simp
  obtain ⟨qc, hqc, hqcc, haqc⟩ := (mem_checkers _ _ _).mp hcm
  have hqcol : qc.color = colorOf (1 - t % 2) := by
    rw [hqcc, run_turn h t hle, colorOf_opp1 (t % 2) hlt2]
  have hkkqc : qc.kind ≠ .king := by
    intro hkkk
    have hqcw : qc = ⟨qc.color, .king⟩ := by cases qc; simp_all
    have hqc' : ((runOf p ms).pos t).board c = some ⟨qc.color, .king⟩ := hqcw ▸ hqc
    have hd1 := king_attack_adjacent _ _ _ _ (hqcw ▸ haqc)
    obtain ⟨hwk, hbk, hku⟩ := run_kings h t hle
    rcases (by omega : t % 2 = 0 ∨ t % 2 = 1) with hpar | hpar
    · have hKw : toSq ((cfgOf w b n m).K (t % 2)) = w := by
        rw [hpar]; show toSq w.val = w; exact toSq_val w
      rw [hKw] at hd1
      have hqcb : qc.color = .black := by rw [hqcol, hpar]; decide
      rw [hqcb] at hqc'
      rcases hku c .black hqc' with hce | hce
      · rw [hce, hwk] at hqc'
        exact absurd (congrArg Piece.color (Option.some.inj hqc')) (by decide)
      · rw [hce, kdist_comm] at hd1
        have hap := run_apart' h
        omega
    · have hKb : toSq ((cfgOf w b n m).K (t % 2)) = b := by
        rw [hpar]; show toSq b.val = b; exact toSq_val b
      rw [hKb] at hd1
      have qccw : qc.color = .white := by rw [hqcol, hpar]; decide
      rw [qccw] at hqc'
      rcases hku c .white hqc' with hce | hce
      · rw [hce] at hd1
        have hap := run_apart' h
        omega
      · rw [hce, hbk] at hqc'
        exact absurd (congrArg Piece.color (Option.some.inj hqc')) (by decide)
  have hgeom0 : geomAttack qc.color qc.kind c (toSq ((cfgOf w b n m).K (t % 2))) = true :=
    ((mem_attacks_iff _ _ _ _).mp haqc).1
  have hkcol : colIdx qc.color = 1 - t % 2 := by
    rw [hqcol, colorOf_colIdx (1 - t % 2) (by omega)]
  have hne12 := run_neK' h t hle c qc hqc hkkqc
  have hKo : ((runOf p ms).pos t).board (toSq ((cfgOf w b n m).K (1 - t % 2))) =
      some ⟨colorOf (1 - t % 2), .king⟩ := run_kingAt' h t hle (1 - t % 2) (by omega)
  have hdisj := lemmaE_single _ _ c hc0 hkk hcl _ hleg hkm
  rcases hdisj with hdc | hec | hsc
  · rw [hdc]
    left
    have npcase : qc.kind = .knight ∨ qc.kind = .pawn →
        (cfgOf w b n m).cand (t % 2) c.val = true := fun hkn =>
      cand_geom_of w b n m (t % 2) hlt2 c qc hkkqc hkn hkcol hgeom0 hne12.1 hne12.2
    have raycase : isSlider qc.kind = true →
        (cfgOf w b n m).cand (t % 2) c.val = true := by
      intro hslx
      have hal := slider_line _ _ _ qc hslx haqc
      rw [aligned_comm] at hal
      have hcp := ((mem_attacks_iff _ _ _ _).mp haqc).2 hslx
      have hsk : c ≠ toSq ((cfgOf w b n m).K (1 - t % 2)) := by
        intro e
        rw [← e] at hKo
        exact hkkqc (congrArg Piece.kind (Option.some.inj (hqc.symm.trans hKo)))
      have hins : inSeg (toSq ((cfgOf w b n m).K (t % 2))) c
          (toSq ((cfgOf w b n m).K (1 - t % 2))) = false := by
        by_cases hi : inSeg (toSq ((cfgOf w b n m).K (t % 2))) c
            (toSq ((cfgOf w b n m).K (1 - t % 2))) = true
        · have h0 := hcp _ ((inSeg_comm _ _ _).symm.trans hi)
          rw [hKo] at h0
          simp at h0
        · exact (Bool.not_eq_true _).mp hi
      exact cand_ray_of w b n m (run_apart' h) (t % 2) hlt2 c hal hsk hins
    cases hkdc : qc.kind with
    | pawn => exact npcase (Or.inr hkdc)
    | knight => exact npcase (Or.inl hkdc)
    | king => exact absurd hkdc hkkqc
    | bishop => exact raycase (by rw [hkdc]; decide)
    | rook => exact raycase (by rw [hkdc]; decide)
    | queen => exact raycase (by rw [hkdc]; decide)
  · obtain ⟨-, -, hvp, -, -, -⟩ := epVictim_spec _ _ c hleg hec
    have hqce : qc = ⟨((runOf p ms).pos t).turn.opp, .pawn⟩ :=
      Option.some.inj (hqc.symm.trans hvp)
    subst hqce
    right
    have hqck : (⟨((runOf p ms).pos t).turn.opp, .pawn⟩ : Piece).kind ≠ .king := by simp
    have hqcol2 : colIdx (⟨((runOf p ms).pos t).turn.opp, .pawn⟩ : Piece).color = 1 - t % 2 := by
      show colIdx ((runOf p ms).pos t).turn.opp = 1 - t % 2
      rw [run_turn h t hle, colorOf_opp1 (t % 2) hlt2, colorOf_colIdx (1 - t % 2) (by omega)]
    have hneK2 := run_neK' h t hle c ⟨((runOf p ms).pos t).turn.opp, .pawn⟩ hvp hqck
    exact ⟨c, hec, cand_geom_of w b n m (t % 2) hlt2 c ⟨((runOf p ms).pos t).turn.opp, .pawn⟩
      hqck (Or.inr rfl) hqcol2 ((mem_attacks_iff _ _ _ _).mp haqc).1 hneK2.1 hneK2.2⟩
  · left
    obtain ⟨hslx, hcp⟩ := attacks_inSeg_slider _ _ _ _ qc hkkqc haqc hsc
    have hal := (inSeg_aligned _ _ _ hsc).2.1
    rw [aligned_comm] at hal
    have hsk : ((runOf p ms).mv t).dst ≠ toSq ((cfgOf w b n m).K (1 - t % 2)) := by
      intro e
      exact legal_not_capture_king _ _ hleg hc0.safe _ (e ▸ hKo)
    have hins : inSeg (toSq ((cfgOf w b n m).K (t % 2))) ((runOf p ms).mv t).dst
        (toSq ((cfgOf w b n m).K (1 - t % 2))) = false := by
      by_cases hi : inSeg (toSq ((cfgOf w b n m).K (t % 2))) ((runOf p ms).mv t).dst
          (toSq ((cfgOf w b n m).K (1 - t % 2))) = true
      · have hA : inSeg (toSq ((cfgOf w b n m).K (t % 2))) c ((runOf p ms).mv t).dst = true :=
          (inSeg_comm _ _ _).symm.trans hsc
        have hB := inSeg_trans _ _ _ _ hA hi
        have h0 := hcp _ ((inSeg_comm _ _ _).trans hB)
        rw [hKo] at h0
        simp at h0
      · exact (Bool.not_eq_true _).mp hi
    exact cand_ray_of w b n m (run_apart' h) (t % 2) hlt2 ((runOf p ms).mv t).dst hal hsk hins

theorem core_r4 (h : ChainAt w b n m p ms) (t : Nat) (ht : t < n) (k : Nat)
    (hk : ∃ q, ((runOf p ms).pos t).board ((runOf p ms).mv t).src = some q ∧
      kindIdx ((((runOf p ms).mv t).promo).getD q.kind) = k)
    (hng : attacksGeom k (t % 2) ((runOf p ms).mv t).dst.val ((cfgOf w b n m).K (1 - t % 2)) = false ∨
      (btw ((runOf p ms).mv t).dst.val ((cfgOf w b n m).K (1 - t % 2))).any (cfgOf w b n m).isK = true) :
    ((cfgOf w b n m).raySquares (1 - t % 2)).contains ((runOf p ms).mv t).src.val = true ∨
      ∃ v, epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some v ∧
        ((cfgOf w b n m).raySquares (1 - t % 2)).contains v.val = true := by
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step h t ht
  have hle : t ≤ n := Nat.le_of_lt ht
  have hlt2 : t % 2 < 2 := Nat.mod_lt t (by decide)
  have h11 : 1 - (1 - t % 2) = t % 2 := by omega
  obtain ⟨q0, hq0, hkq0⟩ := hk
  have hic : inCheck ((runOf p ms).pos (t + 1)) (colorOf (1 - t % 2)) = true := by
    have e : inCheck (play ((runOf p ms).pos t) ((runOf p ms).mv t))
        (((runOf p ms).pos t).turn).opp = true := hgc
    rw [← hstep, run_turn h t hle, colorOf_opp1 (t % 2) hlt2] at e
    exact e
  obtain ⟨kk, hkk1, hatt⟩ := (inCheck_iff _ _).mp hic
  have hkku := run_king_uniq' h (t + 1) (by omega) (1 - t % 2) (by omega) kk hkk1
  subst hkku
  rw [colorOf_opp2 (t % 2) hlt2] at hatt
  obtain ⟨S, qS, hbS, hqSc, haS⟩ := (attacked_iff _ _ _).mp hatt
  have hdst1 : ((runOf p ms).pos (t + 1)).board ((runOf p ms).mv t).dst =
      some ⟨q0.color, ((runOf p ms).mv t).promo.getD q0.kind⟩ := by
    rw [hstep, play_board_dst]
    cases hpr : ((runOf p ms).mv t).promo with
    | none => rw [hq0]; rfl
    | some k0 => rw [hq0]; rfl
  have hq0k : q0.kind ≠ .king := by
    intro e
    have h2 : (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .king) = true := by
      rw [hq0]
      show (q0.kind == .king) = true
      rw [e]
      decide
    have h3 : isKingMove ((runOf p ms).pos t) ((runOf p ms).mv t) = true := h2
    rw [h3] at hkm
    simp at hkm
  have hkk2 : ((runOf p ms).mv t).promo.getD q0.kind ≠ .king := by
    intro e
    cases hpr : ((runOf p ms).mv t).promo with
    | none => rw [hpr] at e; exact hq0k e
    | some k0 =>
      have hpk := promo_ne_king _ _ (legal_mem_pseudo _ _ hleg)
      rw [hpr] at e
      have e2 : k0 = .king := e
      rw [hpr, e2] at hpk
      exact hpk rfl
  have hqSknd0 : qS.kind ≠ .king := by
    intro ek
    have hqcw : qS = ⟨qS.color, .king⟩ := by cases qS; simp_all
    have hd1 := king_attack_adjacent _ _ _ _ (hqcw ▸ haS)
    have hSqa : ((runOf p ms).pos (t + 1)).board S = some ⟨qS.color, .king⟩ := hqcw ▸ hbS
    have hkS : kingAt ((runOf p ms).pos (t + 1)) (colorOf (t % 2)) S := by
      rw [← hqSc]; exact hSqa
    have hKSq := run_king_uniq' h (t + 1) (by omega) (t % 2) hlt2 S hkS
    have hap2 : 2 ≤ kdist (toSq ((cfgOf w b n m).K (t % 2)))
        (toSq ((cfgOf w b n m).K (1 - t % 2))) := by
      rcases (by omega : t % 2 = 0 ∨ t % 2 = 1) with hpar | hpar
      · rw [hpar]
        show 2 ≤ kdist (toSq w.val) (toSq b.val)
        rw [toSq_val, toSq_val]; exact run_apart' h
      · rw [hpar]
        show 2 ≤ kdist (toSq b.val) (toSq w.val)
        rw [toSq_val, toSq_val, kdist_comm]; exact run_apart' h
    rw [hKSq] at hd1
    omega
  rcases core_r1 h t ht S qS hbS hqSc haS with hSd | ⟨z, hzseg, hzsrc⟩
  · exfalso
    rw [hSd] at hbS haS
    have hqSq : qS = ⟨q0.color, ((runOf p ms).mv t).promo.getD q0.kind⟩ :=
      Option.some.inj (hbS.symm.trans hdst1)
    have hqSkind : qS.kind = ((runOf p ms).mv t).promo.getD q0.kind := by
      have e := congrArg Piece.kind hqSq
      exact e
    have hqSknd : qS.kind ≠ .king := by rw [hqSkind]; exact hkk2
    have hgeom1 : geomAttack qS.color qS.kind ((runOf p ms).mv t).dst
        (toSq ((cfgOf w b n m).K (1 - t % 2))) = true :=
      ((mem_attacks_iff _ _ _ _).mp haS).1
    have hqScol : qS.color = q0.color := by
      have e := congrArg Piece.color hqSq
      exact e
    have hq0col : q0.color = colorOf (t % 2) := by rw [← hqScol]; exact hqSc
    have eag := attacksGeom_eq qS hqSknd ((runOf p ms).mv t).dst
      (toSq ((cfgOf w b n m).K (1 - t % 2)))
    rw [hgeom1] at eag
    rw [hqSkind, hkq0, hqScol, hq0col, colorOf_colIdx (t % 2) hlt2,
      cfg_K_toval w b n m (1 - t % 2) (by omega)] at eag
    rcases hng with hngA | hngB
    · rw [eag] at hngA
      simp at hngA
    · obtain ⟨zz, hzz, hzk⟩ := List.any_eq_true.mp hngB
      have hzz2 : zz ∈ btw ((runOf p ms).mv t).dst.val
          (toSq ((cfgOf w b n m).K (1 - t % 2))).val := by
        rw [cfg_K_toval w b n m (1 - t % 2) (by omega)]
        exact hzz
      obtain ⟨hz64, hzseg2⟩ := (mem_btw_iff_nat _ _ _).mp hzz2
      have hkwb : zz = w.val ∨ zz = b.val := by
        have h2 : (zz == w.val || zz == b.val) = true := hzk
        rwa [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h2
      obtain ⟨hk1w, hk1b, -⟩ := run_kings h (t + 1) (by omega)
      obtain ⟨hslM, hclM⟩ := attacks_inSeg_slider _ _ _ _ qS hqSknd haS hzseg2
      have hnone := hclM (toSq zz) hzseg2
      rcases hkwb with hzw | hzb
      · have e : toSq zz = w := by
          apply Fin.ext
          show zz % 64 = w.val
          rw [Nat.mod_eq_of_lt hz64, hzw]
        rw [e, hk1w] at hnone
        simp at hnone
      · have e : toSq zz = b := by
          apply Fin.ext
          show zz % 64 = b.val
          rw [Nat.mod_eq_of_lt hz64, hzb]
        rw [e, hk1b] at hnone
        simp at hnone
  · obtain ⟨hslS, hclS⟩ := attacks_inSeg_slider _ _ _ _ qS hqSknd0 haS hzseg
    have halz : aligned (toSq ((cfgOf w b n m).K (1 - t % 2))) z = true :=
      (inSeg_aligned _ _ _ ((inSeg_comm _ _ _).trans hzseg)).1
    have hKo2b : ((runOf p ms).pos (t + 1)).board (toSq ((cfgOf w b n m).K (t % 2))) =
        some ⟨colorOf (t % 2), .king⟩ := run_kingAt' h (t + 1) (by omega) (t % 2) hlt2
    have hKo1b : ((runOf p ms).pos t).board (toSq ((cfgOf w b n m).K (t % 2))) =
        some ⟨colorOf (t % 2), .king⟩ := run_kingAt' h t hle (t % 2) hlt2
    have hnez : z ≠ toSq ((cfgOf w b n m).K (1 - (1 - t % 2))) := by
      rw [h11]
      rcases hzsrc with hz | hz
      · intro e2
        rw [hz] at e2
        rw [← e2] at hKo1b
        exact hq0k (congrArg Piece.kind (Option.some.inj (hKo1b.symm.trans hq0)) |>.symm)
      · intro e2
        obtain ⟨-, -, hvp, -, -, -⟩ := epVictim_spec _ _ z hleg hz
        rw [← e2] at hKo1b
        have e3 := Option.some.inj (hKo1b.symm.trans hvp)
        rw [run_turn h t hle, colorOf_opp1 (t % 2) hlt2] at e3
        exact Kind.noConfusion (congrArg Piece.kind e3)
    have hinz : inSeg (toSq ((cfgOf w b n m).K (1 - t % 2))) z
        (toSq ((cfgOf w b n m).K (1 - (1 - t % 2)))) = false := by
      rw [h11]
      by_cases hi : inSeg (toSq ((cfgOf w b n m).K (1 - t % 2))) z
          (toSq ((cfgOf w b n m).K (t % 2))) = true
      · have hA : inSeg (toSq ((cfgOf w b n m).K (1 - t % 2))) S z = true :=
          (inSeg_comm _ _ _).trans hzseg
        have hB := inSeg_trans _ _ _ _ hA hi
        have hB2 : inSeg S (toSq ((cfgOf w b n m).K (1 - t % 2)))
            (toSq ((cfgOf w b n m).K (t % 2))) = true := (inSeg_comm _ _ _).trans hB
        have h0 := hclS _ hB2
        rw [hKo2b] at h0
        simp at h0
      · exact (Bool.not_eq_true _).mp hi
    rcases hzsrc with hz | hz
    · left
      rw [← hz]
      exact raySquares_mem_of w b n m (1 - t % 2) (by omega) (run_apart' h) z halz hnez hinz
    · right
      exact ⟨z, hz,
        raySquares_mem_of w b n m (1 - t % 2) (by omega) (run_apart' h) z halz hnez hinz⟩

end Cores

section Localize

variable (g : Cfg) (Ly : Layout) (c : Clause × Fam)

theorem mem_tag (f : Fam) (cs : List Clause) (h : c ∈ tag f cs) : c.2 = f ∧ c.1 ∈ cs := by
  simp only [tag, List.mem_map] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨rfl, hx⟩

theorem mem_clausesOf (h : c ∈ clausesOf g Ly) :
    c ∈ boardPart g Ly ∨ c ∈ attPart g Ly ∨ c ∈ ep0Part g Ly ∨ c ∈ pliesPart g Ly ∨ c ∈ startPart g Ly ∨
      c ∈ chk0Part g Ly ∨ c ∈ perPart g Ly ∨ c ∈ capsPart g Ly ∨ c ∈ redundantCls g Ly := by
  simpa [clausesOf, List.mem_append, or_assoc] using h

theorem tag_fam (f : Fam) (cs : List Clause) (h : c ∈ tag f cs) : c.2 = f := (mem_tag c f cs h).1

theorem boardPart_fam (h : c ∈ boardPart g Ly) : c.2 = .onehot := by
  simp only [boardPart, List.mem_flatMap] at h
  obtain ⟨_, _, h⟩ := h
  exact tag_fam c _ _ h

theorem attCls_fam (L : AttLayer) (h : c ∈ attCls L) : c.2 = .clear ∨ c.2 = .attack := by
  simp only [attCls, List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨_, _, h⟩ | ⟨_, _, h | h⟩
  · exact Or.inl (tag_fam c _ _ h)
  · obtain ⟨_, _, h⟩ := h
    exact Or.inr (tag_fam c _ _ h)
  · exact Or.inr (tag_fam c _ _ h)

theorem attPart_fam (h : c ∈ attPart g Ly) : c.2 = .clear ∨ c.2 = .attack := by
  simp only [attPart, List.mem_flatMap, List.mem_append] at h
  obtain ⟨_, _, h | h⟩ := h <;> exact attCls_fam c _ h

theorem epCls_fam (t : Nat) (X0 : Array (List Int)) (q : Option Ply) (E : List (Nat × Int))
    (h : c ∈ epCls g t X0 q E) : c.2 = .ep := by
  simp only [epCls, List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨x, _, h⟩ | h
  · split at h <;> exact tag_fam c _ _ h
  · split at h
    · exact tag_fam c _ _ h
    · cases h

theorem plyMove1Cls_fam (q : Ply) (h : c ∈ plyMove1Cls g q) : c.2 = .move1 := by
  simp only [plyMove1Cls, List.mem_append] at h
  rcases h with ((h | h) | h) | h <;> exact tag_fam c _ _ h

theorem plyEprCls_fam (t : Nat) (X0 X1 : Array (List Int)) (E : List (Nat × Int)) (q : Ply)
    (h : c ∈ plyEprCls g t X0 X1 E q) : c.2 = .ep := by
  simp only [plyEprCls, List.mem_flatMap] at h
  obtain ⟨x, _, h⟩ := h
  split at h
  · simp at h
  · exact tag_fam c _ _ h

theorem plySqCls_fam (t : Nat) (X0 : Array (List Int)) (q : Ply)
    (h : c ∈ plySqCls g t X0 q) : c.2 = .move1 ∨ c.2 = .source ∨ c.2 = .dest := by
  simp only [plySqCls, List.mem_flatMap, List.mem_append] at h
  obtain ⟨_, _, (h | h) | h⟩ := h
  · exact Or.inl (tag_fam c _ _ h)
  · exact Or.inr (Or.inl (tag_fam c _ _ h))
  · exact Or.inr (Or.inr (tag_fam c _ _ h))

theorem plyPairCls_fam (t : Nat) (X0 : Array (List Int)) (q : Ply) (f hh : Nat)
    (h : c ∈ plyPairCls g t X0 q f hh) : c.2 = .geom ∨ c.2 = .transit ∨ c.2 = .pawn := by
  simp only [plyPairCls] at h
  split at h
  · exact Or.inl (tag_fam c _ _ h)
  · simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · split at h
      · exact Or.inl (tag_fam c _ _ h)
      · simp at h
    · exact Or.inr (Or.inl (tag_fam c _ _ h))
    · split at h
      · split at h
        · exact Or.inr (Or.inr (tag_fam c _ _ h))
        · split at h <;> exact Or.inr (Or.inr (tag_fam c _ _ h))
      · simp at h

theorem plyGeomCls_fam (t : Nat) (X0 : Array (List Int)) (q : Ply)
    (h : c ∈ plyGeomCls g t X0 q) : c.2 = .geom ∨ c.2 = .transit ∨ c.2 = .pawn := by
  simp only [plyGeomCls, List.mem_flatMap] at h
  obtain ⟨f, _, hh, _, hp⟩ := h
  split at hp
  · simp at hp
  · exact plyPairCls_fam g c t X0 q f hh hp

theorem plyCapCls_fam (X0 : Array (List Int)) (q : Ply) (h : c ∈ plyCapCls g X0 q) : c.2 = .cap := by
  simp only [plyCapCls, List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨_, _, h⟩ | h <;> exact tag_fam c _ _ h

theorem plyPromoCls_fam (t : Nat) (q : Ply) (h : c ∈ plyPromoCls g t q) : c.2 = .promo :=
  tag_fam c _ _ h

theorem plyFrameCls_fam (t : Nat) (X0 X1 : Array (List Int)) (q : Ply)
    (h : c ∈ plyFrameCls g t X0 X1 q) : c.2 = .update ∨ c.2 = .frame := by
  simp only [plyFrameCls, List.mem_flatMap, List.mem_append] at h
  obtain ⟨_, _, h | h⟩ := h
  · exact Or.inl (tag_fam c _ _ h)
  · exact Or.inr (tag_fam c _ _ h)

theorem plyCls_fam (t : Nat) (X0 X1 : Array (List Int)) (E : List (Nat × Int)) (q : Ply)
    (h : c ∈ plyCls g t X0 X1 E q) :
    (c.2 = .move1 ∧ (c ∈ plyMove1Cls g q ∨ c ∈ plySqCls g t X0 q)) ∨
    (c.2 = .ep ∧ c ∈ plyEprCls g t X0 X1 E q) ∨
    ((c.2 = .source ∨ c.2 = .dest) ∧ c ∈ plySqCls g t X0 q) ∨
    ((c.2 = .geom ∨ c.2 = .transit ∨ c.2 = .pawn) ∧ c ∈ plyGeomCls g t X0 q) ∨
    (c.2 = .cap ∧ c ∈ plyCapCls g X0 q) ∨
    (c.2 = .promo ∧ c ∈ plyPromoCls g t q) ∨
    ((c.2 = .update ∨ c.2 = .frame) ∧ c ∈ plyFrameCls g t X0 X1 q) := by
  simp only [plyCls, List.mem_append] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inl ⟨plyMove1Cls_fam g c q h, Or.inl h⟩
  · exact Or.inr (Or.inl ⟨plyEprCls_fam g c t X0 X1 E q h, h⟩)
  · rcases plySqCls_fam g c t X0 q h with hf | hf | hf
    · exact Or.inl ⟨hf, Or.inr h⟩
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inl hf, h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inr hf, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨plyGeomCls_fam g c t X0 q h, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨plyCapCls_fam g c X0 q h, h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨plyPromoCls_fam g c t q h, h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨plyFrameCls_fam g c t X0 X1 q h, h⟩)))))

theorem pliesPart_mem (h : c ∈ pliesPart g Ly) : ∃ t, t < g.n ∧
    (c ∈ plyCls g t (Ly.X0 t) (Ly.X0 (t + 1)) (Ly.EPS.getD t []) (Ly.ply t) ∨
      c ∈ epCls g (t + 1) (Ly.X0 (t + 1)) (some (Ly.ply t)) (Ly.EPS.getD (t + 1) [])) := by
  simp only [pliesPart, List.mem_flatMap, List.mem_range, List.mem_append] at h
  obtain ⟨t, ht, h | h⟩ := h
  · exact ⟨t, ht, Or.inl h⟩
  · exact ⟨t, ht, Or.inr h⟩

theorem startPart_fam (h : c ∈ startPart g Ly) : c.2 = .start := by
  simp only [startPart, List.mem_append] at h
  rcases h with h | h <;> exact tag_fam c _ _ h

theorem chk0Part_fam (h : c ∈ chk0Part g Ly) : c.2 = .check := by
  simp only [chk0Part] at h
  split at h
  · exact tag_fam c _ _ h
  · cases h

theorem perPart_fam (h : c ∈ perPart g Ly) : c.2 = .legal ∨ c.2 = .check := by
  simp only [perPart, List.mem_flatMap, List.mem_append] at h
  obtain ⟨_, _, h⟩ := h
  rcases h with (h | h) | h
  · exact Or.inl (tag_fam c _ _ h)
  · exact Or.inr (tag_fam c _ _ h)
  · split at h
    · exact Or.inr (tag_fam c _ _ h)
    · cases h

theorem capsPart_fam (h : c ∈ capsPart g Ly) : c.2 = .capcount := tag_fam c _ _ h

def famSrc (g : Cfg) (Ly : Layout) : Fam → List (Clause × Fam)
  | .onehot => boardPart g Ly
  | .clear | .attack => attPart g Ly
  | .ep => ep0Part g Ly ++ (List.range g.n).flatMap fun t =>
      plyEprCls g t (Ly.X0 t) (Ly.X0 (t + 1)) (Ly.EPS.getD t []) (Ly.ply t) ++
        epCls g (t + 1) (Ly.X0 (t + 1)) (some (Ly.ply t)) (Ly.EPS.getD (t + 1) [])
  | .move1 => (List.range g.n).flatMap fun t => plyMove1Cls g (Ly.ply t) ++ plySqCls g t (Ly.X0 t) (Ly.ply t)
  | .source | .dest => (List.range g.n).flatMap fun t => plySqCls g t (Ly.X0 t) (Ly.ply t)
  | .geom | .transit | .pawn => (List.range g.n).flatMap fun t => plyGeomCls g t (Ly.X0 t) (Ly.ply t)
  | .cap => (List.range g.n).flatMap fun t => plyCapCls g (Ly.X0 t) (Ly.ply t)
  | .promo => (List.range g.n).flatMap fun t => plyPromoCls g t (Ly.ply t)
  | .update | .frame => (List.range g.n).flatMap fun t => plyFrameCls g t (Ly.X0 t) (Ly.X0 (t + 1)) (Ly.ply t)
  | .start => startPart g Ly
  | .check => chk0Part g Ly ++ perPart g Ly
  | .legal => perPart g Ly
  | .capcount => capsPart g Ly
  | .r1 | .r2 | .r3 | .r4 => redundantCls g Ly

theorem redundant_parts (h : c ∈ redundantCls g Ly) : ∃ t, t < g.n ∧
    ((c.2 = .r1 ∧ c.1 ∈ r1Cls g Ly t) ∨ (c.2 = .r4 ∧ c.1 ∈ r4Cls g Ly t) ∨
      (c.2 = .r2 ∧ c.1 ∈ r2Cls g Ly t) ∨ (c.2 = .r3 ∧ c.1 ∈ r3Cls g Ly t)) := by
  simp only [redundantCls, List.mem_flatMap, List.mem_range, List.mem_append] at h
  obtain ⟨t, ht, ((h | h) | h) | h⟩ := h
  · obtain ⟨hf, hm⟩ := mem_tag c _ _ h
    exact ⟨t, ht, Or.inl ⟨hf, hm⟩⟩
  · obtain ⟨hf, hm⟩ := mem_tag c _ _ h
    exact ⟨t, ht, Or.inr (Or.inl ⟨hf, hm⟩)⟩
  · obtain ⟨hf, hm⟩ := mem_tag c _ _ h
    exact ⟨t, ht, Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))⟩
  · obtain ⟨hf, hm⟩ := mem_tag c _ _ h
    exact ⟨t, ht, Or.inr (Or.inr (Or.inr ⟨hf, hm⟩))⟩

theorem mem_famSrc (h : c ∈ clausesOf g Ly) : c ∈ famSrc g Ly c.2 := by
  rcases mem_clausesOf g Ly c h with h | h | h | h | h | h | h | h | h
  · rw [boardPart_fam g Ly c h]
    exact h
  · rcases attPart_fam g Ly c h with hf | hf <;> rw [hf] <;> exact h
  · rw [epCls_fam g c _ _ _ _ h]
    exact List.mem_append_left _ h
  · rcases pliesPart_mem g Ly c h with ⟨t, ht, hpl | hep⟩
    · rcases plyCls_fam g c t _ _ _ _ hpl with
        ⟨hf, hm | hm⟩ | ⟨hf, hm⟩ | ⟨hf | hf, hm⟩ | ⟨hf | hf | hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
          ⟨hf | hf, hm⟩
      all_goals
        rw [hf]
        first
          | exact List.mem_append_right _
              (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, List.mem_append_left _ hm⟩)
          | exact List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, List.mem_append_left _ hm⟩
          | exact List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, List.mem_append_right _ hm⟩
          | exact List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, hm⟩
    · rw [epCls_fam g c _ _ _ _ hep]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, List.mem_append_right _ hep⟩)
  · rw [startPart_fam g Ly c h]
    exact h
  · rw [chk0Part_fam g Ly c h]
    exact List.mem_append_left _ h
  · rcases perPart_fam g Ly c h with hf | hf
    · rw [hf]
      exact h
    · rw [hf]
      exact List.mem_append_right _ h
  · rw [capsPart_fam g Ly c h]
    exact h
  · rcases redundant_parts g Ly c h with ⟨t, -, hf | hf | hf | hf⟩ <;> rw [hf.1] <;> exact h

theorem mem_plyGeomCls (t : Nat) (X0 : Array (List Int)) (q : Ply) (h : c ∈ plyGeomCls g t X0 q) :
    ∃ f ∈ g.NK, ∃ h' ∈ g.NK, f ≠ h' ∧ c ∈ plyPairCls g t X0 q f h' := by
  simp only [plyGeomCls, List.mem_flatMap] at h
  obtain ⟨f, hf, h', hh', hp⟩ := h
  split at hp
  · simp at hp
  · rename_i hne
    exact ⟨f, hf, h', hh', hne, hp⟩

theorem mem_plySqCls (t : Nat) (X0 : Array (List Int)) (q : Ply) (h : c ∈ plySqCls g t X0 q) :
    ∃ s ∈ g.NK, c ∈ tag .move1 [[-q.fr s, -q.to s]] ∨
      c ∈ tag .source ((-q.fr s :: (List.range 5).map fun p => xv X0 s (5 * g.col t + p)) ::
        (List.range 5).flatMap fun p => [[-q.fr s, -q.mp p, xv X0 s (5 * g.col t + p)],
          [-q.fr s, -xv X0 s (5 * g.col t + p), q.mp p]]) ∨
      c ∈ tag .dest ((List.range 5).map fun p => [-q.to s, -xv X0 s (5 * g.col t + p)]) := by
  simp only [plySqCls, List.mem_flatMap, List.mem_append] at h
  obtain ⟨s, hs, (h | h) | h⟩ := h
  · exact ⟨s, hs, Or.inl h⟩
  · exact ⟨s, hs, Or.inr (Or.inl h)⟩
  · exact ⟨s, hs, Or.inr (Or.inr h)⟩

theorem zip_pair_getD {α β : Type} [Inhabited α] [Inhabited β] {l₁ : List α} {l₂ : List β}
    {a : α} {b : β} (h : (a, b) ∈ l₁.zip l₂) :
    ∃ i, i < l₁.length ∧ i < l₂.length ∧ l₁.getD i default = a ∧ l₂.getD i default = b := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with heq | h
      · obtain ⟨rfl, rfl⟩ := heq
        exact ⟨0, Nat.succ_pos _, Nat.succ_pos _, List.getD_cons_zero, List.getD_cons_zero⟩
      · obtain ⟨i, h1, h2, h3, h4⟩ := ih h
        refine ⟨i + 1, by simp only [List.length_cons]; omega,
          by simp only [List.length_cons]; omega, ?_, ?_⟩
        · rw [List.getD_cons_succ]; exact h3
        · rw [List.getD_cons_succ]; exact h4

theorem mem_plyFrameCls (t : Nat) (X0 X1 : Array (List Int)) (q : Ply) (h : c ∈ plyFrameCls g t X0 X1 q) :
    ∃ i, i < g.NK.length ∧ i < q.CH.length ∧
      let s := g.NK.getD i 0
      let ch := q.CH.getD i 0
      let lits := [q.fr s, q.to s] ++ (look q.EPR s).toList
      c ∈ tag .update ([-q.fr s, xv X1 s EMP] :: (List.range 5).map fun p => [-q.to s, -q.rt p, xv X1 s (5 * g.col t + p)]) ∨
      c ∈ tag .frame ((-ch :: lits) :: lits.map (fun l => [-l, ch]) ++
        (List.range 11).flatMap fun k => [[ch, -xv X0 s k, xv X1 s k], [ch, xv X0 s k, -xv X1 s k]]) := by
  simp only [plyFrameCls, List.mem_flatMap, List.mem_append] at h
  obtain ⟨⟨s, ch⟩, hmem, h | h⟩ := h
  all_goals obtain ⟨i, h1, h2, hsD, hchD⟩ := zip_pair_getD hmem
  all_goals have hs0 : g.NK.getD i 0 = s := hsD
  all_goals have hch0 : q.CH.getD i 0 = ch := hchD
  all_goals refine ⟨i, h1, h2, ?_⟩
  all_goals simp only [hs0, hch0]
  · exact Or.inl h
  · exact Or.inr h

theorem mem_attCls (L : AttLayer) (h : c ∈ attCls L) :
    (∃ tr ∈ L.clears, c ∈ tag .clear [[-tr.1, tr.2.1], [-tr.1, tr.2.2], [tr.1, -tr.2.1, -tr.2.2]]) ∨
    (∃ en ∈ L.entries, (∃ la ∈ en.conjs, c ∈ tag .attack ((la.1.map Neg.neg ++ [en.a]) ::
        match la.2 with
        | none => []
        | some v => la.1.map (fun l => [-v, l]) ++ [la.1.map Neg.neg ++ [v]])) ∨
      c ∈ tag .attack [-en.a :: en.conjs.map fun la => la.2.getD (la.1.getD 0 0)]) := by
  simp only [attCls, List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨tr, htr, h⟩ | ⟨en, hen, ⟨la, hla, h⟩ | h⟩
  · exact Or.inl ⟨tr, htr, h⟩
  · exact Or.inr ⟨en, hen, Or.inl ⟨la, hla, h⟩⟩
  · exact Or.inr ⟨en, hen, Or.inr h⟩

theorem redundant_mem (h : c ∈ redundantCls g Ly) : ∃ t, t < g.n ∧
    ((c.2 = .r1 ∧ c.1 ∈ r1Cls g Ly t) ∨ (c.2 = .r4 ∧ c.1 ∈ r4Cls g Ly t) ∨
      (c.2 = .r2 ∧ c.1 ∈ r2Cls g Ly t) ∨ (c.2 = .r3 ∧ c.1 ∈ r3Cls g Ly t)) :=
  redundant_parts g Ly c h

end Localize

section Families

def FamOK (w b : Sq) (n m : Nat) (fam : Fam) : Prop :=
  1 ≤ n → ∀ p ms, ChainAt w b n m p ms → ∀ c ∈ (encode w b n m).cls, c.2 = fam →
    Clause.eval (intended (encode w b n m) (runOf p ms)) c.1 = true

variable (w b : Sq) (n m : Nat)

namespace X13

theorem fa2_map_of {α β γ : Type} (R : β → γ → Prop) (f : α → β) (v : α → γ) :
    ∀ (l : List α), (∀ a ∈ l, R (f a) (v a)) → Fa2 R (l.map f) (l.map v)
  | [], _ => trivial
  | _ :: xs, h => ⟨h _ List.mem_cons_self, fa2_map_of R f v xs (fun a ha => h a (List.mem_cons_of_mem _ ha))⟩

theorem cnt_beq_nodup (v : Nat) : ∀ (l : List Nat), l.Nodup →
    ((l.map fun s => (v == s)).filter id).length ≤ 1 := by
  intro l
  induction l with
  | nil => intro; simp
  | cons x xs ih =>
    intro hn
    rw [List.nodup_cons] at hn
    obtain ⟨hx, hxs⟩ := hn
    simp only [List.map_cons]
    cases hvx : (v == x)
    · rw [List.filter_cons_of_neg (by decide)]
      exact ih hxs
    · have hxv : v = x := beq_iff_eq.mp hvx
      rw [List.filter_cons_of_pos (by rfl)]
      have hflt : ((xs.map fun s => (v == s)).filter id) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b' hb
        simp only [List.mem_map] at hb
        obtain ⟨s, hs, rfl⟩ := hb
        intro hsv
        have hsx : x = s := beq_iff_eq.mp (hxv ▸ hsv)
        exact absurd (hsx ▸ hs) hx
      rw [hflt]
      simp

theorem list_eq_range_getD {α : Type} (d : α) : ∀ (l : List α),
    l = (List.range l.length).map fun i => l.getD i d
  | [] => rfl
  | _ :: xs => by
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
      rw [← list_eq_range_getD d xs]

theorem take_any_map_sem (g : Cfg) (r : Run) (f : Nat → Sem) (v : Nat → Bool) (l : List Nat) (k : Nat)
    (h : ∀ s ∈ l, (f s).val g r = v s) :
    ((l.map f).take k).any (fun a => a.val g r) = ((l.map v).take k).any id := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have e1 := h x List.mem_cons_self
      have e2 := ih k (fun s hs => h s (List.mem_cons_of_mem _ hs))
      simp [List.map_cons, List.take_succ_cons, List.any_cons, e1, e2]

theorem mem_getD' {α : Type} (d : α) {a : α} : ∀ {l : List α}, a ∈ l → ∃ i, i < l.length ∧ l.getD i d = a
  | _ :: xs, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, Nat.succ_pos _, List.getD_cons_zero⟩
      · obtain ⟨i, hi, hget⟩ := mem_getD' d h
        exact ⟨i + 1, Nat.succ_lt_succ hi, by rw [List.getD_cons_succ]; exact hget⟩
  | [], h => absurd h (by simp)

theorem mem_of_look {l : List (Nat × Int)} {r : Nat} {v : Int} (h : look l r = some v) : (r, v) ∈ l := by
  cases hf : l.find? (fun e => e.1 == r) with
  | none => rw [look, hf] at h; simp at h
  | some ab =>
    rw [look, hf] at h
    simp at h
    have h1 := List.find?_some hf
    have h2 : ab ∈ l := List.mem_of_find?_eq_some hf
    have hae : ab.1 = r := beq_iff_eq.mp h1
    obtain ⟨a', b'⟩ := ab
    simp only at hae h
    rw [← hae, ← h]
    exact h2

theorem exists_look_of_keys {l : List (Nat × Int)} {r : Nat} (h : r ∈ l.map (·.1)) : ∃ v, look l r = some v := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.map_cons, List.mem_cons] at h
    rcases h with h | h
    · rw [h]
      exact ⟨x.2, by simp [look]⟩
    · obtain ⟨v, hv⟩ := ih h
      cases hx : (x.1 == r)
      · exact ⟨v, by simp only [look]; rw [List.find?_cons, hx]; exact hv⟩
      · exact ⟨x.2, by simp [look, hx]⟩

theorem nk_nodup (g : Cfg) : g.NK.Nodup := by
  show ((List.range 64).filter _).Nodup
  unfold List.Nodup
  exact List.nodup_range.filter _

theorem colIdx_colorOf (x : Nat) (hx : x < 2) : colIdx (colorOf x) = x := by
  obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
  · rfl
  · rfl

theorem eq_colorOf_colIdx (c : Color) (x : Nat) (hx : x < 2) (h : colIdx c = x) : c = colorOf x := by
  obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
  · cases c <;> first | rfl | simp [colIdx, colorOf] at h
  · cases c <;> first | rfl | simp [colIdx, colorOf] at h

theorem kindIdx_lt_of_ne_king (k : Kind) (h : k ≠ .king) : kindIdx k < 5 := by
  cases k <;> first | decide | exact absurd rfl h

theorem kindIdx_eq_P (k : Kind) (h : kindIdx k = P) : k = .pawn := by
  cases k <;> simp [P, kindIdx] at h ⊢

theorem code_nonking (qc : Color) (qk : Kind) (hk : qk ≠ .king) :
    code (some ⟨qc, qk⟩) = 5 * colIdx qc + kindIdx qk := by
  cases qk <;> first | rfl | exact absurd rfl hk

theorem code_ne_emp_of_some (q : Piece) : (code (some q) == EMP) = false := by
  obtain ⟨c', k'⟩ := q
  cases c' <;> cases k' <;> decide

theorem board_none_of_code_emp (b' : Option Piece) (h : code b' = EMP) : b' = none := by
  cases b' with
  | none => rfl
  | some q => exact absurd (code_ne_emp_of_some q ▸ beq_iff_eq.mpr h) (by decide)

theorem code_of_eq (b' : Option Piece) (x p : Nat) (hx : x < 2) (hp : p < 5) (h : code b' = 5 * x + p) :
    ∃ c' k', b' = some ⟨c', k'⟩ ∧ colIdx c' = x ∧ kindIdx k' = p := by
  cases b' with
  | none =>
    have : code (none : Option Piece) = 10 := rfl
    rw [this] at h
    omega
  | some q =>
    obtain ⟨c', k'⟩ := q
    by_cases hk' : k' = .king
    · subst hk'
      exfalso
      have e : code (some ⟨c', .king⟩) = 11 := rfl
      rw [e] at h
      omega
    · rw [code_nonking c' k' hk'] at h
      have h1 : colIdx c' < 2 := by cases c' <;> decide
      have hk5' : kindIdx k' < 5 := kindIdx_lt_of_ne_king k' hk'
      exact ⟨c', k', rfl, by omega, by omega⟩

theorem isEmpty_nil {α : Type} {l : List α} (h : l.isEmpty = true) : l = [] := by
  cases l <;> simp [List.isEmpty] at h ⊢

theorem clause_eval₆ (σ : Assign) (a b d e f i : Int) :
    Clause.eval σ [a, b, d, e, f, i] =
      (Lit.eval σ a || (Lit.eval σ b || (Lit.eval σ d || (Lit.eval σ e || (Lit.eval σ f || Lit.eval σ i))))) := by
  simp [Clause.eval]

theorem clause_eval₄ (σ : Assign) (a b d e : Int) :
    Clause.eval σ [a, b, d, e] = (Lit.eval σ a || (Lit.eval σ b || (Lit.eval σ d || Lit.eval σ e))) := by
  simp [Clause.eval]

theorem clause_eval₅ (σ : Assign) (a b d e f : Int) :
    Clause.eval σ [a, b, d, e, f] =
      (Lit.eval σ a || (Lit.eval σ b || (Lit.eval σ d || (Lit.eval σ e || Lit.eval σ f)))) := by
  simp [Clause.eval]

theorem clause_true {σ : Assign} {cl : Clause} {l : Int} (hm : l ∈ cl) (he : Lit.eval σ l = true) :
    Clause.eval σ cl = true := List.any_eq_true.mpr ⟨l, hm, he⟩

theorem plyMove1Cls_eq (g : Cfg) (q : Ply) :
    plyMove1Cls g q =
      tag .move1 (g.NK.map q.fr :: amoCls (g.NK.map q.fr) q.FRL) ++
        tag .move1 (g.NK.map q.to :: amoCls (g.NK.map q.to) q.TOL) ++
        tag .move1 (q.MP :: amoCls q.MP []) ++ tag .move1 (q.RT :: amoCls q.RT []) := rfl

theorem mem_plyMove1Cls (g : Cfg) (c : Clause × Fam) (q : Ply) (h : c ∈ plyMove1Cls g q) :
    c.1 = g.NK.map q.fr ∨ c.1 ∈ amoCls (g.NK.map q.fr) q.FRL ∨
      c.1 = g.NK.map q.to ∨ c.1 ∈ amoCls (g.NK.map q.to) q.TOL ∨
      c.1 = q.MP ∨ c.1 ∈ amoCls q.MP [] ∨ c.1 = q.RT ∨ c.1 ∈ amoCls q.RT [] := by
  rw [plyMove1Cls_eq] at h
  simp only [List.mem_append, or_assoc] at h
  rcases h with h | h | h | h
  all_goals obtain ⟨x, hx, hxc⟩ := List.mem_map.mp h
  all_goals cases hxc
  all_goals simp only [List.mem_cons] at hx
  all_goals rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr (Or.inl hx))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))))

theorem plyPairCls_eq (g : Cfg) (t : Nat) (X0 : Array (List Int)) (q : Ply) (f h : Nat) :
    plyPairCls g t X0 q f h =
      (if (g.allowed (g.col t) f h).isEmpty then tag .geom [[-q.fr f, -q.to h]]
       else
        (if (g.allowed (g.col t) f h).length < 5 then
          tag .geom [[-q.fr f, -q.to h] ++ (g.allowed (g.col t) f h).map q.mp]
         else []) ++
        tag .transit ((btw f h).map fun s => [-q.fr f, -q.to h, xv X0 s EMP]) ++
        (if (g.allowed (g.col t) f h).contains P then
          if fl f = fl h then tag .pawn [[-q.fr f, -q.to h, -q.mp P, xv X0 h EMP]]
          else
            match look q.EPR (sqOf (fl h) (rk h - pdir (g.col t))) with
            | some v => tag .pawn [[-q.fr f, -q.to h, -q.mp P, -xv X0 h EMP, v]]
            | none => tag .pawn [[-q.fr f, -q.to h, -q.mp P, -xv X0 h EMP]]
         else [])) := rfl

theorem mem_plyPairCls (g : Cfg) (t : Nat) (X0 : Array (List Int)) (q : Ply) (f h : Nat)
    (c : Clause × Fam) (hp : c ∈ plyPairCls g t X0 q f h) :
    ((g.allowed (g.col t) f h).isEmpty = true ∧ c ∈ tag .geom [[-q.fr f, -q.to h]]) ∨
    ((g.allowed (g.col t) f h).isEmpty = false ∧ (g.allowed (g.col t) f h).length < 5 ∧
      c ∈ tag .geom [[-q.fr f, -q.to h] ++ (g.allowed (g.col t) f h).map q.mp]) ∨
    (c ∈ tag .transit ((btw f h).map fun s => [-q.fr f, -q.to h, xv X0 s EMP])) ∨
    (((g.allowed (g.col t) f h).contains P = true ∧ fl f = fl h ∧
      c ∈ tag .pawn [[-q.fr f, -q.to h, -q.mp P, xv X0 h EMP]])) ∨
    (((g.allowed (g.col t) f h).contains P = true ∧ fl f ≠ fl h ∧
      ((∃ v, look q.EPR (sqOf (fl h) (rk h - pdir (g.col t))) = some v ∧
          c ∈ tag .pawn [[-q.fr f, -q.to h, -q.mp P, -xv X0 h EMP, v]]) ∨
        (look q.EPR (sqOf (fl h) (rk h - pdir (g.col t))) = none ∧
          c ∈ tag .pawn [[-q.fr f, -q.to h, -q.mp P, -xv X0 h EMP]])))) := by
  rw [plyPairCls_eq] at hp
  by_cases he : (g.allowed (g.col t) f h).isEmpty = true
  · rw [if_pos he] at hp
    exact Or.inl ⟨he, hp⟩
  · have hef : (g.allowed (g.col t) f h).isEmpty = false := by
      cases hbb : (g.allowed (g.col t) f h).isEmpty <;> simp_all
    rw [if_neg he] at hp
    simp only [List.mem_append, or_assoc] at hp
    rcases hp with hp | hp | hp
    · by_cases hl5 : (g.allowed (g.col t) f h).length < 5
      · rw [if_pos hl5] at hp
        exact Or.inr (Or.inl ⟨hef, hl5, hp⟩)
      · rw [if_neg hl5] at hp
        simp at hp
    · exact Or.inr (Or.inr (Or.inl hp))
    · by_cases hcon : (g.allowed (g.col t) f h).contains P = true
      · rw [if_pos hcon] at hp
        by_cases hfl : fl f = fl h
        · rw [if_pos hfl] at hp
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hcon, hfl, hp⟩)))
        · rw [if_neg hfl] at hp
          split at hp
          · rename_i v hlo
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hcon, hfl, Or.inl ⟨v, hlo, hp⟩⟩)))
          · rename_i hlo
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hcon, hfl, Or.inr ⟨hlo, hp⟩⟩)))
      · rw [if_neg hcon] at hp
        simp at hp

end X13

namespace X12

variable (g : Cfg)

abbrev AB := Array (List Int) × Array (List Int)

def bstep12 (t : Nat) (acc : AB) (s : Nat) : AM AB := do
  let rs := (List.range 11).map fun k => Sem.x t s k
  let xs ← freshMany (rs.map .sem)
  let lad ← amoAlloc rs
  pure (acc.1.set! s xs, acc.2.set! s lad)

theorem boardAlloc_eq (t : Nat) : boardAlloc g t =
    (forIn g.NK (Array.replicate 64 [], Array.replicate 64 []) fun s acc => do
      let rs := (List.range 11).map fun k => Sem.x t s k
      let xs ← freshMany (rs.map .sem)
      let lad ← amoAlloc rs
      pure (ForInStep.yield (acc.1.set! s xs, acc.2.set! s lad))) := rfl

theorem inner_body_run_eq (t : Nat) (s : Nat) (acc : AB) (a : Alloc) :
    ((do
        let rs := (List.range 11).map fun k => Sem.x t s k
        let xs ← freshMany (rs.map .sem)
        let lad ← amoAlloc rs
        pure (ForInStep.yield (acc.1.set! s xs, acc.2.set! s lad))).run a) =
      ((ForInStep.yield <$> bstep12 t acc s).run a) := by
  unfold bstep12
  simp only [X6.run_map, X6.run_bind, X6.run_pure, freshMany_run, List.length_map,
    List.length_range]

theorem inner_body_eq (t : Nat) :
    (fun s acc => do
        let rs := (List.range 11).map fun k => Sem.x t s k
        let xs ← freshMany (rs.map .sem)
        let lad ← amoAlloc rs
        pure (ForInStep.yield (acc.1.set! s xs, acc.2.set! s lad))) =
      (fun s acc => ForInStep.yield <$> bstep12 t acc s) := by
  funext s acc
  exact StateT.ext fun a => inner_body_run_eq t s acc a

theorem boardAlloc_fold (t : Nat) : boardAlloc g t =
    (g.NK).foldlM (fun acc s => bstep12 t acc s) (Array.replicate 64 [], Array.replicate 64 []) := by
  rw [boardAlloc_eq, inner_body_eq, X6.forIn_yield]

theorem getD_set_self' (X : Array (List Int)) (i : Nat) (v : List Int) (h : i < X.size) :
    (X.set! i v).getD i [] = v := by
  rw [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getD_getElem?_setIfInBounds,
    ite_eq_left h]

theorem getD_set_ne' (X : Array (List Int)) (i j : Nat) (v : List Int) (h : i ≠ j) :
    (X.set! i v).getD j [] = X.getD j [] := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, ite_eq_right h]

theorem bstep12_run1 (t : Nat) (acc : AB) (s : Nat) (a : Alloc) :
    ((bstep12 t acc s).run a).1 =
      (acc.1.set! s ((List.range 11).map fun i => ((a.nv + i + 1 : Nat) : Int)),
       acc.2.set! s ((amoAlloc ((List.range 11).map fun k => Sem.x t s k)).run
         (((freshMany (((List.range 11).map fun k => Sem.x t s k).map .sem)).run a).2)).1) := by
  unfold bstep12
  simp only [X6.run_bind, X6.run_pure, freshMany_run, List.length_map, List.length_range]

theorem bstep12_getD_self (t : Nat) (acc : AB) (s : Nat) (a : Alloc) (hs : s < acc.1.size) :
    ((((bstep12 t acc s).run a).1).1.getD s []).length = 11 := by
  rw [bstep12_run1]
  show ((acc.1.set! s ((List.range 11).map fun i => ((a.nv + i + 1 : Nat) : Int))).getD s []).length = 11
  rw [getD_set_self' _ _ _ hs]
  simp [List.length_map]

theorem bstep12_getD_ne (t : Nat) (acc : AB) (s s' : Nat) (a : Alloc) (hne : s ≠ s') :
    (((bstep12 t acc s).run a).1).1.getD s' [] = acc.1.getD s' [] := by
  rw [bstep12_run1]
  show ((acc.1.set! s ((List.range 11).map fun i => ((a.nv + i + 1 : Nat) : Int))).getD s' []) =
    acc.1.getD s' []
  exact getD_set_ne' _ _ _ _ hne

theorem inner_len (t : Nat) : ∀ (done cur : List Nat) (acc : AB) (a : Alloc),
    g.NK = done ++ cur → acc.1.size = 64 → (∀ s ∈ done, (acc.1.getD s []).length = 11) →
    ∀ s ∈ g.NK, (((cur.foldlM (fun acc s => bstep12 t acc s) acc).run a).1.1.getD s []).length = 11 := by
  intro done cur acc a hNK hsz hIn
  induction cur generalizing done acc a with
  | nil =>
    intro s hs
    rw [List.foldlM_nil, X6.run_pure]
    rw [List.append_nil] at hNK
    exact hIn s (hNK ▸ hs)
  | cons x xs ih =>
    intro s hs
    rw [List.foldlM_cons, X6.run_bind]
    have hxNK : x ∈ g.NK := hNK ▸ List.mem_append_right _ (List.mem_cons_self)
    have hx64 : x < 64 := List.mem_range.mp (List.mem_filter.mp hxNK).1
    have hne : ∀ u ∈ done, u ≠ x := by
      intro u hud hux
      have hnd := X13.nk_nodup g
      rw [hNK, List.nodup_append] at hnd
      exact hnd.2.2 u hud x List.mem_cons_self hux
    exact ih (done ++ [x]) ((bstep12 t acc x).run a).1 ((bstep12 t acc x).run a).2
      (by rw [hNK, List.append_assoc] <;> rfl)
      (by rw [show (((bstep12 t acc x).run a).1).1 = acc.1.set! x ((List.range 11).map fun i =>
              ((a.nv + i + 1 : Nat) : Int)) from by rw [bstep12_run1],
            Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz])
      (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · rw [bstep12_getD_ne t acc x u a (fun h => (hne u hu) h.symm)]
          exact hIn u hu
        · rw [List.mem_singleton.mp hu]
          have hs6 : x < acc.1.size := by rw [hsz]; exact hx64
          rw [bstep12_run1]
          show ((acc.1.set! x ((List.range 11).map fun i => ((a.nv + i + 1 : Nat) : Int))).getD x []).length = 11
          rw [getD_set_self' _ _ _ hs6]
          simp [List.length_map])
      s hs


abbrev A2 := Array (Array (List Int)) × Array (Array (List Int))

def bSt : Nat → Alloc
  | 0 => { nv := 0, roles := #[] }
  | t + 1 => ((boardAlloc g t).run (bSt t)).2

def bVal (t : Nat) : Array (List Int) := ((boardAlloc g t).run (bSt g t)).1.1

def lVal (t : Nat) : Array (List Int) := ((boardAlloc g t).run (bSt g t)).1.2

theorem bRes_eq (t : Nat) : (boardAlloc g t).run (bSt g t) = ((bVal g t, lVal g t), bSt g (t + 1)) := rfl

def bdStep (t : Nat) (s : A2) : AM A2 :=
  (fun v => (s.1.push v.1, s.2.push v.2)) <$> boardAlloc g t

theorem L1_body_run (t : Nat) (s : A2) (a : Alloc) :
    ((do
        let __x ← boardAlloc g t
        match __x with | (a1, b1) => pure (ForInStep.yield (s.1.push a1, s.2.push b1))).run a) =
      ((ForInStep.yield <$> bdStep g t s).run a) := by
  generalize (boardAlloc g t).run a = r
  obtain ⟨v, a2⟩ := r
  obtain ⟨x1, x2⟩ := v
  simp only [X6.run_pure]
  rfl

theorem L1_body_eq :
    (fun (t : Nat) (__s : A2) => do
        let __x ← boardAlloc g t
        match __x with | (a1, b1) => pure (ForInStep.yield (__s.1.push a1, __s.2.push b1))) =
      fun t __s => ForInStep.yield <$> bdStep g t __s := by
  funext t s
  exact StateT.ext fun a => L1_body_run g t s a

theorem L1_fold : X6.L1 g = (List.range (g.n + 1)).foldlM (fun acc t => bdStep g t acc) (#[], #[]) := by
  rw [X6.L1, L1_body_eq g, X6.forIn_yield]

theorem L1_run : ∀ k : Nat,
    ((List.range k).foldlM (fun acc t => bdStep g t acc) ((#[], #[]) : A2)).run (bSt g 0) =
      ((((List.range k).map (bVal g)).toArray, ((List.range k).map (lVal g)).toArray), bSt g k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [X6.foldlM_range_succ, X6.run_bind, ih]
    show ((((fun v : Array (List Int) × Array (List Int) => (((List.range k).map (bVal g)).toArray.push v.1,
            ((List.range k).map (lVal g)).toArray.push v.2))) <$> boardAlloc g k).run (bSt g k)) =
        ((((List.range (k + 1)).map (bVal g)).toArray, ((List.range (k + 1)).map (lVal g)).toArray),
          bSt g (k + 1))
    rw [X6.run_map, bRes_eq]
    show ((((List.range k).map (bVal g)).toArray.push (bVal g k),
        ((List.range k).map (lVal g)).toArray.push (lVal g k)), bSt g (k + 1)) =
      ((((List.range (k + 1)).map (bVal g)).toArray, ((List.range (k + 1)).map (lVal g)).toArray),
        bSt g (k + 1))
    rw [X5.rangeMapArr_push, X5.rangeMapArr_push]

theorem L1_full : (X6.L1 g).run { nv := 0, roles := #[] } =
    ((((List.range (g.n + 1)).map (bVal g)).toArray, ((List.range (g.n + 1)).map (lVal g)).toArray),
      bSt g (g.n + 1)) := by
  rw [L1_fold]
  exact L1_run g (g.n + 1)

theorem tail_X (XXL : A2) (AT : Array (Array AttLayer))
    (EP : Array (List (Nat × Int)) × Array Ply) (a : Alloc) :
    ((X6.tail g XXL AT EP).run a).1.X = XXL.1 := by
  by_cases h : g.n ≥ 1
  · rw [X6.tail_eq_ge g XXL AT EP h]
    simp only [X6.run_bind, X6.run_pure]
    rw [X6.restAfterL0]
    rfl
  · rw [X6.tail_eq_ite]
    simp only [ite_eq_right h, X6.run_bind, X6.run_pure]
    rw [X6.restAfterL0]
    rfl

theorem layoutX_eq : (encodeCfg g).layout.X = ((List.range (g.n + 1)).map (bVal g)).toArray := by
  obtain ⟨XXL, AT, e0, EP, a1, a2, ae, aP, b1, b2, be, bp, _hsz, _hpl⟩ := X6.decomp g
  have hXXL1 : XXL.1 = ((List.range (g.n + 1)).map (bVal g)).toArray := by
    have h2 := b1.symm.trans (L1_full g)
    injection h2 with hXXL _
    rw [hXXL]
  have hlay : (encodeCfg g).layout = ((X6.tail g XXL AT EP).run aP).1 := by
    rw [X6.encodeCfg_layout, X6.layoutM_eq]
    simp only [X6.run_bind]
    rw [b1, b2, be, bp]
  rw [hlay, tail_X g XXL AT EP aP, hXXL1]

theorem xEntry (t : Nat) (ht : t ≤ g.n) : (encodeCfg g).layout.X.getD t #[] = bVal g t := by
  rw [layoutX_eq, X5.rangeMapArr_getD (bVal g) #[] (g.n + 1) t (by omega)]

theorem bVal_length (t : Nat) (s : Nat) (hs : s ∈ g.NK) : ((bVal g t).getD s []).length = 11 := by
  show ((((boardAlloc g t).run (bSt g t)).1.1.getD s [])).length = 11
  rw [boardAlloc_fold]
  exact inner_len g t [] g.NK _ _ (List.nil_append _).symm (by simp) (fun _ hs => by simp at hs) s hs

theorem xlen (t : Nat) (ht : t ≤ g.n) (s : Nat) (hs : s ∈ g.NK) :
    (((encodeCfg g).layout.X.getD t #[]).getD s []).length = 11 := by
  rw [xEntry g t ht]
  exact bVal_length g t s hs

theorem xshape (t : Nat) (ht : t ≤ g.n) (s : Nat) (hs : s ∈ g.NK) :
    ((encodeCfg g).layout.X.getD t #[]).getD s [] =
      (List.range 11).map fun k => xv ((encodeCfg g).layout.X.getD t #[]) s k := by
  rw [X13.list_eq_range_getD (0 : Int) (((encodeCfg g).layout.X.getD t #[]).getD s []), xlen g t ht s hs]
  apply List.map_congr_left
  intro k _
  rfl


theorem orli (A B C : Bool) (h : C = (A && B)) :
    (!C || A) = true ∧ (!C || B) = true ∧ (C || (!A || !B)) = true := by
  cases A <;> cases B <;> simp_all

theorem attClears_len (g : Cfg) (x : Nat) (ss : List Nat) (h : ss ∈ attClears g x) : 2 ≤ ss.length := by
  simp only [attClears, List.mem_flatMap] at h
  obtain ⟨d, hd, h⟩ := h
  simp only [List.mem_map] at h
  obtain ⟨j, hj, rfl⟩ := h
  rw [List.mem_filter] at hj
  rw [List.length_take]
  have hj2 : 2 ≤ j := of_decide_eq_true hj.2
  have hjl : j < (g.ray x d).length := List.mem_range.mp hj.1
  omega

theorem opp_colorOf (x : Nat) (hx : x < 2) : colorOf (1 - x) = (colorOf x).opp := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rfl

theorem kingAtC0 (pos : Pos) (hkw : kingAt pos .white w) (hbk : kingAt pos .black b) (x : Nat)
    (hx : x < 2) : kingAt pos (colorOf x) (toSq ((cfgOf w b n m).K x)) := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
  · have e : toSq ((cfgOf w b n m).K 0) = w := toSq_val w
    rw [e]
    exact hkw
  · have e : toSq ((cfgOf w b n m).K 1) = b := toSq_val b
    rw [e]
    exact hbk

theorem perPart_tail (g : Cfg) (Ly : Layout) (t : Nat) (c : Clause × Fam)
    (h : c ∈ (if t + 1 ≤ g.n - 1 then
        tag .check (amoCls ((Ly.att (t + 1) (1 - g.col t)).A.map fun x => x.snd) (Ly.LS.getD t []))
      else [])) :
    t + 1 ≤ g.n - 1 ∧
      c ∈ tag .check (amoCls ((Ly.att (t + 1) (1 - g.col t)).A.map fun x => x.snd) (Ly.LS.getD t [])) := by
  by_cases hspl : t + 1 ≤ g.n - 1
  · rw [if_pos hspl] at h
    exact ⟨hspl, h⟩
  · rw [if_neg hspl] at h
    simp at h

theorem take_any_congr {α : Type} (g : Cfg) (r : Run) (f : α → Sem) (v : α → Bool) (l : List α) (k : Nat)
    (h : ∀ a ∈ l, (f a).val g r = v a) :
    ((l.map f).take k).any (fun a => a.val g r) = ((l.map v).take k).any id := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have e1 := h x List.mem_cons_self
      have e2 := ih k (fun s hs => h s (List.mem_cons_of_mem _ hs))
      simp [List.map_cons, List.take_succ_cons, List.any_cons, e1, e2]

theorem cnt_unique {α : Type} (l : List α) (P : α → Bool) (key : α → Nat) (hnd : (l.map key).Nodup)
    (hu : ∀ a ∈ l, ∀ b ∈ l, P a = true → P b = true → key a = key b) :
    ((l.map P).filter id).length ≤ 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hx, hxs⟩ := hnd
    simp only [List.map_cons]
    cases hvx : P x
    · rw [List.filter_cons_of_neg (by decide)]
      exact ih hxs (fun a ha b hb => hu a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    · rw [List.filter_cons_of_pos (by rfl)]
      have hflt : ((xs.map P).filter id) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b' hb
        obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hb
        intro hsv
        have hsx : key x = key s' :=
          hu x List.mem_cons_self s' (List.mem_cons_of_mem _ hs') hvx hsv
        exact hx (List.mem_map.mpr ⟨s', hs', hsx.symm⟩)
      rw [hflt]
      simp

theorem insertAlt_lt (al : List (Nat × List (List ALit))) (s : Nat) (cc : List ALit)
    (hal : ∀ k ∈ al.map (·.1), k < 64) (hs : s < 64) :
    ∀ k ∈ (insertAlt al s cc).map (·.1), k < 64 := by
  rw [insertAlt_keys]
  split
  · exact hal
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hal k hk
    · rw [List.mem_singleton.mp hk]
      exact hs

theorem foldl_keys_lt {α : Type} (P : α → Prop)
    (step : List (Nat × List (List ALit)) → α → List (Nat × List (List ALit)))
    (hst : ∀ al a, P a → (∀ k ∈ al.map (·.1), k < 64) → ∀ k ∈ (step al a).map (·.1), k < 64) :
    ∀ (l : List α) (init : List (Nat × List (List ALit))),
    (∀ a ∈ l, P a) → (∀ k ∈ init.map (·.1), k < 64) →
      ∀ k ∈ ((l.foldl step init).map (·.1)), k < 64 := by
  intro l
  induction l with
  | nil => intro init _ h; exact h
  | cons x xs ih =>
    intro init hP h0
    rw [List.foldl_cons]
    exact ih (step init x) (fun a ha => hP a (List.mem_cons_of_mem _ ha))
      (hst init x (hP x List.mem_cons_self) h0)

def npStep (g : Cfg) (x : Nat) : List (Nat × List (List ALit)) → Nat → List (Nat × List (List ALit)) :=
  fun al s =>
    let al := if attacksGeom N (1 - x) s (g.K x) then insertAlt al s [.x s (5 * (1 - x) + N)] else al
    if attacksGeom P (1 - x) s (g.K x) then insertAlt al s [.x s (5 * (1 - x) + P)] else al

def daStep (g : Cfg) (x : Nat) :
    List (Nat × List (List ALit)) → Int × Int → List (Nat × List (List ALit)) := fun al d =>
  let sl := if orth.contains d then R else B
  let ray := g.ray x d
  (List.range ray.length).foldl (fun al j =>
    [Q, sl].foldl (fun al p => insertAlt al (ray.getD j 0) ((clearLit ray j).toList ++
      [.x (ray.getD j 0) (5 * (1 - x) + p)])) al) al

theorem attAlts_eq' (g : Cfg) (x : Nat) :
    attAlts g x = (orth ++ diag).foldl (daStep g x) (g.NK.foldl (npStep g x) []) := rfl

theorem attAlts_keys_lt (g : Cfg) (hw : g.kw < 64) (hb : g.kb < 64) (x : Nat) (hx : x < 2) :
    ∀ k ∈ (attAlts g x).map (·.1), k < 64 := by
  have hK : g.K x < 64 := by
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
    · show g.kw < 64; exact hw
    · show g.kb < 64; exact hb
  rw [attAlts_eq']
  apply foldl_keys_lt (P := fun d => d ∈ orth ++ diag)
  · intro al d hd hal
    show ∀ k ∈ ((daStep g x al d).map (·.1)), k < 64
    apply foldl_keys_lt (P := fun j => j < (g.ray x d).length)
    · intro al' j hj hal'
      apply foldl_keys_lt (P := fun _ => True)
      · intro al'' p _ hal''
        exact insertAlt_lt al'' _ _ hal'' (ray_getD g x d hd hK j hj).1
      · intro _ _; trivial
      · exact hal'
    · intro j hj; exact List.mem_range.mp hj
    · exact hal
  · intro d hd; exact hd
  · apply foldl_keys_lt (P := fun s => s < 64)
    · intro al s hs hal
      show ∀ k ∈ ((npStep g x al s).map (·.1)), k < 64
      show ∀ k ∈ ((if attacksGeom P (1 - x) s (g.K x) then insertAlt (if attacksGeom N (1 - x) s (g.K x) then insertAlt al s [.x s (5 * (1 - x) + N)] else al) s [.x s (5 * (1 - x) + P)] else (if attacksGeom N (1 - x) s (g.K x) then insertAlt al s [.x s (5 * (1 - x) + N)] else al)).map (·.1)), k < 64
      by_cases h1 : attacksGeom N (1 - x) s (g.K x) = true
      · rw [if_pos h1]
        by_cases h2 : attacksGeom P (1 - x) s (g.K x) = true
        · rw [if_pos h2]
          exact insertAlt_lt _ _ _ (insertAlt_lt _ _ _ hal hs) hs
        · rw [if_neg h2]
          exact insertAlt_lt _ _ _ hal hs
      · rw [if_neg h1]
        by_cases h2 : attacksGeom P (1 - x) s (g.K x) = true
        · rw [if_pos h2]
          exact insertAlt_lt _ _ _ hal hs
        · rw [if_neg h2]
          exact hal
    · intro s hs
      exact List.mem_range.mp (List.mem_filter.mp hs).1
    · intro k hk
      simp at hk

theorem Amap2 (L : AttLayer) : L.A.map (·.2) = L.entries.map (·.a) := by
  simp only [AttLayer.A, List.map_map, Function.comp_def]

theorem Amapatt (t x : Nat) (L : AttLayer) :
    L.A.map (fun sa => Sem.att t x sa.1) = L.entries.map fun en => Sem.att t x en.s := by
  simp only [AttLayer.A, List.map_map, Function.comp_def]


theorem att_uniq (p : Pos) (ms : List Move) (hch : ChainAt w b n m p ms) (t' : Nat) (ht' : t' < n) (x : Nat) (hx : x < 2)
    (hpm : t' % 2 = x) :
    ∀ a ∈ (attAtL (cfgOf w b n m) t' x).entries, ∀ b2 ∈ (attAtL (cfgOf w b n m) t' x).entries,
      (Sem.att t' x a.s).val (cfgOf w b n m) (runOf p ms) = true →
      (Sem.att t' x b2.s).val (cfgOf w b n m) (runOf p ms) = true → a.s = b2.s := by
  intro a ha b2 hb ha1 hb1
  have klt := attAlts_keys_lt (cfgOf w b n m) (by exact w.isLt) (by exact b.isLt) x hx
  have hkeys : (attAtL (cfgOf w b n m) t' x).entries.map (·.s) = (attAlts (cfgOf w b n m) x).map (·.1) :=
    (roles_entries (cfgOf w b n m) t' x (Nat.le_of_lt ht') hx).1
  have ha64 : a.s < 64 := by
    apply klt
    rw [← hkeys]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hb64 : b2.s < 64 := by
    apply klt
    rw [← hkeys]
    exact List.mem_map.mpr ⟨b2, hb, rfl⟩
  have ha2 : (Sem.att t' (t' % 2) a.s).val (cfgOf w b n m) (runOf p ms) = true := by
    rw [hpm]; exact ha1
  have hb2 : (Sem.att t' (t' % 2) b2.s).val (cfgOf w b n m) (runOf p ms) = true := by
    rw [hpm]; exact hb1
  have h := core_single hch t' ht' a.s b2.s ha2 hb2
  have := congrArg Fin.val h
  simp only [toSq] at this
  rwa [Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt hb64] at this

theorem hamo_att (p : Pos) (ms : List Move) (hch : ChainAt w b n m p ms) (t' : Nat) (ht' : t' < n) (x : Nat) (hx : x < 2)
    (hpm : t' % 2 = x) :
    ((((attAtL (cfgOf w b n m) t' x).entries.map fun en =>
      (Sem.att t' x en.s).val (cfgOf w b n m) (runOf p ms)).filter id)).length ≤ 1 := by
  apply cnt_unique _ _ (·.s)
  · rw [(roles_entries (cfgOf w b n m) t' x (Nat.le_of_lt ht') hx).1]
    exact attAlts_keys_nodup _ _
  · exact att_uniq w b n m p ms hch t' ht' x hx hpm

theorem fa2_attA (p : Pos) (ms : List Move) (t' x : Nat) (ht' : t' ≤ n) (hx : x < 2) :
    Fa2 (fun l v => Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) l = v)
      ((attAtL (cfgOf w b n m) t' x).entries.map (·.a))
      ((attAtL (cfgOf w b n m) t' x).entries.map fun en =>
        (Sem.att t' x en.s).val (cfgOf w b n m) (runOf p ms)) := by
  apply X13.fa2_map_of
  intro en hen
  obtain ⟨cs0, hcs0, hA, hf2⟩ := (roles_entries (cfgOf w b n m) t' x ht' hx).2 en hen
  exact (lit_pos _ _ _ _ hA).trans rfl

theorem kingSqK (pos : Pos) (hkAll : ∀ s cc, pos.board s = some ⟨cc, .king⟩ → s = w ∨ s = b)
    (hkw : kingAt pos .white w) (hbk : kingAt pos .black b) (x : Nat) (hx : x < 2) (k' : Sq)
    (hk : kingAt pos (colorOf x) k') : k' = toSq ((cfgOf w b n m).K x) := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
  · rw [show toSq ((cfgOf w b n m).K 0) = w from toSq_val w]
    rcases hkAll k' _ hk with hk' | hk'
    · exact hk'
    · exfalso
      rw [hk'] at hk
      have hk2 : pos.board b = (some ⟨colorOf 0, .king⟩ : Option Piece) := hk
      have hbb : pos.board b = (some ⟨.black, .king⟩ : Option Piece) := hbk
      rw [hk2] at hbb
      have h4 : colorOf 0 = Color.black := by
        rw [Option.some.injEq, Piece.mk.injEq] at hbb
        exact hbb.1
      exact absurd h4 (by decide)
  · rw [show toSq ((cfgOf w b n m).K 1) = b from toSq_val b]
    rcases hkAll k' _ hk with hk' | hk'
    · exfalso
      rw [hk'] at hk
      have hk2 : pos.board w = (some ⟨colorOf 1, .king⟩ : Option Piece) := hk
      have hkw2 : pos.board w = (some ⟨.white, .king⟩ : Option Piece) := hkw
      rw [hk2] at hkw2
      have h4 : colorOf 1 = Color.white := by
        rw [Option.some.injEq, Piece.mk.injEq] at hkw2
        exact hkw2.1
      exact absurd h4 (by decide)
    · exact hk'

set_option maxHeartbeats 2000000 in
theorem nodup_pair_val {β : Type} (l : List (Nat × β)) (hnd : (l.map (·.1)).Nodup) (k : Nat)
    (a b : β) (ha : (k, a) ∈ l) (hb : (k, b) ∈ l) : a = b := by
  induction l with
  | nil => simp at ha
  | cons p ps ih =>
    obtain ⟨pk, pv⟩ := p
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hp, hps⟩ := hnd
    rcases List.mem_cons.mp ha with ha2 | ha2
    · rw [Prod.mk.injEq] at ha2
      obtain ⟨hk1, rfl⟩ := ha2
      subst hk1
      rcases List.mem_cons.mp hb with hb2 | hb2
      · rw [Prod.mk.injEq] at hb2
        exact hb2.2.symm
      · exfalso
        exact hp (List.mem_map.mpr ⟨(k, b), hb2, rfl⟩)
    · rcases List.mem_cons.mp hb with hb2 | hb2
      · rw [Prod.mk.injEq] at hb2
        obtain ⟨hk2, -⟩ := hb2
        subst hk2
        exfalso
        exact hp (List.mem_map.mpr ⟨(k, a), ha2, rfl⟩)
      · exact ih hps ha2 hb2

theorem exists_false_of_all_false {α : Type} (l : List α) (p : α → Bool)
    (h : l.all p = false) : ∃ a ∈ l, p a = false := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.all_cons] at h
    cases hx : p x
    · exact ⟨x, List.mem_cons_self, hx⟩
    · rw [hx, Bool.true_and] at h
      obtain ⟨a, ha, hp⟩ := ih h
      exact ⟨a, List.mem_cons_of_mem _ ha, hp⟩

theorem fa2_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Fa2 R as bs →
      ∀ {b : β}, b ∈ bs → ∃ a, a ∈ as ∧ R a b
  | [], [], _, _, hb => by simp at hb
  | [], _ :: _, h, _, _ => by simp [Fa2] at h
  | x :: as, y :: ys, h, _, hb => by
      have h1 : R x y ∧ Fa2 R as ys := h
      rcases List.mem_cons.mp hb with rfl | hy
      · exact ⟨x, List.mem_cons_self, h1.1⟩
      · obtain ⟨a, ha, hr⟩ := fa2_mem_right h1.2 hy
        exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩
  | _ :: _, [], h, _, _ => by simp [Fa2] at h



end X12

theorem fam_onehot : FamOK w b n m .onehot := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, boardPart, List.mem_flatMap, List.mem_range] at hfm
  obtain ⟨t, ht, h⟩ := hfm
  obtain ⟨-, hm⟩ := mem_tag c .onehot _ h
  simp only [boardCls, List.mem_flatMap] at hm
  obtain ⟨s, hs, hm⟩ := hm
  rw [List.mem_cons] at hm
  have ht' : t ≤ n := by
    have ht0 : t < (cfgOf w b n m).n + 1 := ht
    simp only [cfgOf] at ht0
    omega
  have hshape : ((encodeCfg (cfgOf w b n m)).layout.X0 t).getD s [] =
      (List.range 11).map fun k => xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k :=
    X12.xshape (cfgOf w b n m) t ht' s hs
  have hcode : code (((runOf p ms).pos t).board (toSq s)) < 11 := core_code hch t ht' s hs
  rcases hm with hm | hm
  · rw [hm]
    have hrole : HasRole (encodeCfg (cfgOf w b n m))
        (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s (code (((runOf p ms).pos t).board (toSq s))))
        (.sem (Sem.x t s (code (((runOf p ms).pos t).board (toSq s))))) :=
      roles_X (cfgOf w b n m) t s (code (((runOf p ms).pos t).board (toSq s))) ht' hs hcode
    have hmem : xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s (code (((runOf p ms).pos t).board (toSq s)))
        ∈ ((encodeCfg (cfgOf w b n m)).layout.X0 t).getD s [] := by
      rw [hshape]
      exact List.mem_map.mpr ⟨_, List.mem_range.mpr hcode, rfl⟩
    apply X13.clause_true hmem
    refine (lit_pos _ _ _ _ hrole).trans ?_
    show (code (((runOf p ms).pos t).board (toSq s)) == code (((runOf p ms).pos t).board (toSq s))) = true
    exact beq_self_eq_true _
  · have hL := roles_XL (cfgOf w b n m) t s ht' hs
    apply amo_sound _ _ _
      ((List.range 11).map fun k => (code (((runOf p ms).pos t).board (toSq s)) == k)) _ _ _ _ _ _ hm
    · intro l hl
      rw [hshape] at hl
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
      have h0 : 0 < xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k :=
        (roles_X (cfgOf w b n m) t s k ht' hs (List.mem_range.mp hk)).1
      omega
    · intro l hl
      obtain ⟨i, hi, hget⟩ := X13.mem_getD' 0 hl
      have hi' : i < 10 := by
        have e := hL.1
        omega
      rw [← hget]
      have h0 : 0 < ((((encodeCfg (cfgOf w b n m)).layout.XL.getD t #[]).getD s []).getD i 0) :=
        (hL.2 i hi').1
      omega
    · rw [hshape]
      exact X13.fa2_map_of _ _ _ _ fun k hk =>
        (lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t s k ht' hs (List.mem_range.mp hk))).trans rfl
    · exact X13.cnt_beq_nodup _ _ List.nodup_range
    · intro h8
      constructor
      · rw [hL.1, hshape]
        simp [List.length_map]
      · intro i hi
        have hi' : i < 10 := by
          have e := hL.1
          omega
        refine (lit_pos _ _ _ _ (hL.2 i hi')).trans ?_
        show ((((List.range 11).map (Sem.x t s)).take (i + 1)).any fun a =>
            a.val (cfgOf w b n m) (runOf p ms)) =
          (((List.range 11).map fun k =>
            (code (((runOf p ms).pos t).board (toSq s)) == k)).take (i + 1)).any id
        exact X13.take_any_map_sem _ _ _ _ _ _ fun k _ => rfl


theorem fam_clear : FamOK w b n m .clear := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, attPart, List.mem_flatMap, List.mem_range, List.mem_append] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  have ht' : t ≤ n := by
    have ht0 : t < (cfgOf w b n m).n + 1 := ht
    simp only [cfgOf] at ht0
    omega
  have aux : ∀ x : Nat, x < 2 → c ∈ attCls ((encodeCfg (cfgOf w b n m)).layout.att t x) →
      Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) c.1 = true := by
    intro x hx h
    rcases mem_attCls c _ h with
      ⟨tr, htr, hm⟩ | ⟨en, hen, hm⟩
    · obtain ⟨ss, hss, h1', h2', h3'⟩ := roles_clears (cfgOf w b n m) t x ht' hx tr htr
      obtain ⟨-, hm2⟩ := mem_tag c .clear _ hm
      have hss2 : 2 ≤ ss.length := X12.attClears_len (cfgOf w b n m) x ss hss
      have hu := core_clear (runOf p ms) (cfgOf w b n m) t ss hss2
      have hA : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) tr.2.1 =
          (((clearLit ss (ss.length - 1)).getD (ALit.x 0 0)).sem t).val (cfgOf w b n m) (runOf p ms) :=
        lit_pos _ _ _ _ h2'
      have hB : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) tr.2.2 =
          (Sem.x t (ss.getD (ss.length - 1) 0) EMP).val (cfgOf w b n m) (runOf p ms) :=
        lit_pos _ _ _ _ h3'
      have hC : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (-tr.1) =
          !(Sem.clear t ss).val (cfgOf w b n m) (runOf p ms) := lit_neg _ _ _ _ h1'
      have hCpos : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) tr.1 =
          (Sem.clear t ss).val (cfgOf w b n m) (runOf p ms) := lit_pos _ _ _ _ h1'
      rcases List.mem_cons.mp hm2 with hm2 | hm2
      · rw [hm2, clause_eval₂, hC, hA]
        exact (X12.orli _ _ _ hu).1
      · rcases List.mem_cons.mp hm2 with hm2 | hm2
        · rw [hm2, clause_eval₂, hC, hB]
          exact (X12.orli _ _ _ hu).2.1
        · rw [List.mem_singleton.mp hm2, clause_eval₃, hCpos,
            lit_neg _ _ _ _ h2', lit_neg _ _ _ _ h3']
          show (Sem.val (cfgOf w b n m) (runOf p ms) (Sem.clear t ss) ||
              (!(((clearLit ss (ss.length - 1)).getD (ALit.x 0 0)).sem t).val (cfgOf w b n m)
                  (runOf p ms) ||
                !(Sem.x t (ss.getD (ss.length - 1) 0) EMP).val (cfgOf w b n m) (runOf p ms))) = true
          exact (X12.orli _ _ _ hu).2.2
    · rcases hm with ⟨la, hla, hm⟩ | hm
      · obtain ⟨hf2, -⟩ := mem_tag c .attack _ hm
        rw [hf2] at hf
        exact absurd hf (by decide)
      · obtain ⟨hf2, -⟩ := mem_tag c .attack _ hm
        rw [hf2] at hf
        exact absurd hf (by decide)
  rcases hfm with hfm | hfm
  · exact aux 0 (by decide) hfm
  · exact aux 1 (by decide) hfm


set_option maxHeartbeats 2000000 in
theorem fam_attack : FamOK w b n m .attack := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, attPart, List.mem_flatMap, List.mem_range, List.mem_append] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  have ht' : t ≤ n := by
    have ht0 : t < (cfgOf w b n m).n + 1 := ht
    simp only [cfgOf] at ht0
    omega
  have au2 : ∀ x : Nat, x < 2 → c ∈ attCls ((encodeCfg (cfgOf w b n m)).layout.att t x) →
      Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) c.1 = true := by
    intro x hx h
    rcases mem_attCls c _ h with ⟨tr, htr, hm⟩ | ⟨en, hen, hm⟩
    · obtain ⟨hf2, -⟩ := mem_tag c .clear _ hm
      rw [hf2] at hf
      exact absurd hf (by decide)
    · obtain ⟨cs, hcs, hA, hfa2⟩ := (roles_entries (cfgOf w b n m) t x ht' hx).2 en
        (show en ∈ (attAtL (cfgOf w b n m) t x).entries from hen)
      have evA : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) en.a =
          (Sem.att t x en.s).val (cfgOf w b n m) (runOf p ms) :=
        lit_pos (encodeCfg (cfgOf w b n m)) (runOf p ms) en.a _ hA
      rcases hm with ⟨la, hla, hm⟩ | hm
      · obtain ⟨-, hm2⟩ := mem_tag c .attack _ hm
        obtain ⟨al, hal, hR⟩ := fa2_mem_left hfa2 hla
        obtain ⟨hRlit, hRnone, hRsome⟩ := hR
        by_cases hall : (al.all fun a => (a.sem t).val (cfgOf w b n m) (runOf p ms)) = true
        · have hAt := core_att_sound hch t x ht' hx en.s cs hcs al hal hall
          rw [hAt] at evA
          rcases List.mem_cons.mp hm2 with hm2 | hm2
          · rw [hm2]
            exact X13.clause_true (List.mem_append_right _ List.mem_cons_self) evA
          · cases hla2 : la.2 with
            | none =>
              rw [hla2] at hm2
              have hm2' : c.1 ∈ ([] : List Clause) := hm2
              simp at hm2'
            | some v =>
              have hV := hRsome v hla2
              rw [hla2] at hm2
              have hm2' : c.1 ∈ (la.1.map (fun l => [-v, l]) ++ [la.1.map Neg.neg ++ [v]]) := hm2
              rcases List.mem_append.mp hm2' with hm2 | hm2
              · obtain ⟨l, hl, hle⟩ := List.mem_map.mp hm2
                rw [← hle]
                show Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) [-v, l] = true
                rw [clause_eval₂]
                obtain ⟨aL, haL, hRL⟩ := fa2_mem_left hRlit hl
                have haLt : ((aL.sem t).val (cfgOf w b n m) (runOf p ms)) = true :=
                  (List.all_eq_true.mp hall) aL haL
                rw [show Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) l = true from
                    (lit_pos (encodeCfg (cfgOf w b n m)) (runOf p ms) l _ hRL).trans haLt,
                  Bool.or_true]
              · rw [List.mem_singleton.mp hm2]
                apply X13.clause_true (List.mem_append_right _ List.mem_cons_self)
                have evVt : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) v = true := by
                  rw [lit_pos (encodeCfg (cfgOf w b n m)) (runOf p ms) v _ hV]
                  show ((al.map (ALit.sem t)).all fun a => a.val (cfgOf w b n m) (runOf p ms)) = true
                  rw [List.all_map]
                  show (al.all fun a => (a.sem t).val (cfgOf w b n m) (runOf p ms)) = true
                  exact hall
                exact evVt
        · have hfl : (al.all fun a => (a.sem t).val (cfgOf w b n m) (runOf p ms)) = false := by
            cases h2 : (al.all fun a => (a.sem t).val (cfgOf w b n m) (runOf p ms))
            · rfl
            · exact absurd h2 hall
          obtain ⟨a0, ha0, hv0⟩ := X12.exists_false_of_all_false _ _ hfl
          obtain ⟨l0, hl0, hR0⟩ := X12.fa2_mem_right hRlit ha0
          have hvl0 : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (-l0) = true := by
            rw [lit_neg (encodeCfg (cfgOf w b n m)) (runOf p ms) l0 _ hR0]
            show (!((a0.sem t).val (cfgOf w b n m) (runOf p ms))) = true
            rw [hv0]
            rfl
          rcases List.mem_cons.mp hm2 with hm2 | hm2
          · rw [hm2]
            exact X13.clause_true (List.mem_append_left _ (List.mem_map.mpr ⟨l0, hl0, rfl⟩)) hvl0
          · cases hla2 : la.2 with
            | none =>
              rw [hla2] at hm2
              have hm2' : c.1 ∈ ([] : List Clause) := hm2
              simp at hm2'
            | some v =>
              rw [hla2] at hm2
              have hV := hRsome v hla2
              have hm2' : c.1 ∈ (la.1.map (fun l => [-v, l]) ++ [la.1.map Neg.neg ++ [v]]) := hm2
              rcases List.mem_append.mp hm2' with hm2 | hm2
              · obtain ⟨l, hl, hle⟩ := List.mem_map.mp hm2
                rw [← hle]
                show Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) [-v, l] = true
                rw [clause_eval₂]
                have e1 : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (-v) = true := by
                  rw [lit_neg (encodeCfg (cfgOf w b n m)) (runOf p ms) v _ hV]
                  show (!((al.map (ALit.sem t)).all fun a => a.val (cfgOf w b n m) (runOf p ms))) = true
                  rw [show ((al.map (ALit.sem t)).all fun a => a.val (cfgOf w b n m) (runOf p ms)) =
                      false from by
                    rw [List.all_map]
                    show (al.all fun a => (a.sem t).val (cfgOf w b n m) (runOf p ms)) = false
                    exact hfl]
                  rfl
                rw [e1]
                rfl
              · rw [List.mem_singleton.mp hm2]
                exact X13.clause_true (List.mem_append_left _ (List.mem_map.mpr ⟨l0, hl0, rfl⟩)) hvl0
      · obtain ⟨-, hm2⟩ := mem_tag c .attack _ hm
        rw [List.mem_singleton.mp hm2]
        by_cases hAt : (Sem.att t x en.s).val (cfgOf w b n m) (runOf p ms) = true
        · have hen64 : en.s < 64 :=
            X12.attAlts_keys_lt (cfgOf w b n m) (by exact w.isLt) (by exact b.isLt) x hx en.s
              (List.mem_map.mpr ⟨(en.s, cs), hcs, rfl⟩)
          obtain ⟨cs', hcs', conj', hconj', hv'⟩ :=
            core_att_complete hch t x ht' hx en.s hen64 hAt
          have hkey := attAlts_keys_nodup (cfgOf w b n m) x
          have hcs2 : cs = cs' := X12.nodup_pair_val _ hkey en.s cs cs' hcs hcs'
          subst hcs2
          obtain ⟨cj, hcj, hR⟩ := X12.fa2_mem_right hfa2 hconj'
          obtain ⟨hRlit, hRnone, hRsome⟩ := hR
          apply X13.clause_true (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨cj, hcj, rfl⟩))
          cases hcj2 : cj.2 with
          | some v =>
            show Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
              ((some v).getD (cj.1.getD 0 0)) = true
            rw [Option.getD_some]
            have hV := hRsome v hcj2
            rw [lit_pos (encodeCfg (cfgOf w b n m)) (runOf p ms) v _ hV]
            show ((conj'.map (ALit.sem t)).all fun a => a.val (cfgOf w b n m) (runOf p ms)) = true
            rw [List.all_map]
            show (conj'.all fun a => (a.sem t).val (cfgOf w b n m) (runOf p ms)) = true
            exact hv'
          | none =>
            show Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
              (none.getD (cj.1.getD 0 0)) = true
            rw [Option.getD_none]
            have hlen1 : conj'.length = 1 := hRnone.mp hcj2
            have h09 : 0 < cj.1.length := by
              have hleneq := fa2_length_eq hRlit
              omega
            have h0 : HasRole (encodeCfg (cfgOf w b n m)) (cj.1.getD 0 0)
                (.sem ((conj'.getD 0 (ALit.x 0 0)).sem t)) := fa2_getD hRlit 0 h09 0 (ALit.x 0 0)
            rw [lit_pos (encodeCfg (cfgOf w b n m)) (runOf p ms) _ _ h0]
            show ((conj'.getD 0 (ALit.x 0 0)).sem t).val (cfgOf w b n m) (runOf p ms) = true
            exact (List.all_eq_true.mp hv') _ (getD_mem _ _ _ (by omega))
        · have hfl : (Sem.att t x en.s).val (cfgOf w b n m) (runOf p ms) = false := by
            cases h2 : (Sem.att t x en.s).val (cfgOf w b n m) (runOf p ms)
            · rfl
            · exact absurd h2 hAt
          exact X13.clause_true List.mem_cons_self (by
            rw [lit_neg (encodeCfg (cfgOf w b n m)) (runOf p ms) en.a _ hA]
            show (!(Sem.att t x en.s).val (cfgOf w b n m) (runOf p ms)) = true
            rw [hfl]
            rfl)
  rcases hfm with hfm | hfm
  · exact au2 0 (by decide) hfm
  · exact au2 1 (by decide) hfm


namespace X14

theorem kindIdx_beq_P (k : Kind) : (kindIdx k == P) = (k == .pawn) := by
  cases k <;> decide

theorem any_kindIdx_pawn (b : Option Piece) :
    b.any (fun q => kindIdx q.kind == P) = b.any (fun q => q.kind == .pawn) := by
  cases b with
  | none => rfl
  | some q => show (kindIdx q.kind == P) = (q.kind == .pawn); exact kindIdx_beq_P q.kind

theorem filter_length_le {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = true → q a = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have h' : ∀ a ∈ xs, p a = true → q a = true := fun a ha => h a (List.mem_cons_of_mem _ ha)
    have hx := h x List.mem_cons_self
    by_cases hpx : p x = true
    · have hqx : q x = true := hx hpx
      rw [List.filter_cons_of_pos hpx, List.filter_cons_of_pos hqx, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ (ih h')
    · rw [List.filter_cons_of_neg hpx]
      by_cases hqx : q x = true
      · rw [List.filter_cons_of_pos hqx, List.length_cons]
        exact Nat.le_succ_of_le (ih h')
      · rw [List.filter_cons_of_neg hqx]
        exact ih h'

theorem cnt_eps_le1 (ep : Option Sq) : ∀ (l : List (Nat × Int)), (l.map (·.1)).Nodup →
    (∀ x ∈ l, x.1 < 64) → ((l.map fun sv => (ep == some (toSq sv.1))).filter id).length ≤ 1 := by
  intro l
  induction l with
  | nil => intro; simp
  | cons x xs ih =>
    intro hn hb
    rw [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hxnin, hxs⟩ := hn
    have hb' : ∀ a ∈ xs, a.1 < 64 := fun a ha => hb a (List.mem_cons_of_mem _ ha)
    have hxb := hb x List.mem_cons_self
    simp only [List.map_cons]
    cases hv : (ep == some (toSq x.1))
    · rw [List.filter_cons_of_neg (by decide)]
      exact ih hxs hb'
    · rw [List.filter_cons_of_pos (by decide)]
      have htl : ((xs.map fun sv => (ep == some (toSq sv.1))).filter id) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hbb hbv
        simp only [List.mem_map] at hbb
        obtain ⟨sv, hsv, rfl⟩ := hbb
        have e1 := beq_iff_eq.mp hbv
        have e2 := beq_iff_eq.mp hv
        rw [e2] at e1
        have e3 := Option.some.inj e1
        have e4 : x.1 % 64 = sv.1 % 64 := congrArg Fin.val e3
        have e5 : sv.1 = x.1 := by
          have h1 := hb' sv hsv
          omega
        exact hxnin (e5 ▸ List.mem_map.mpr ⟨sv, hsv, rfl⟩)
      rw [htl]
      simp

theorem filter_filter_length_le {α : Type} (l : List α) (P Q : α → Bool) :
    ((l.filter Q).filter P).length ≤ (l.filter P).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hQ : Q x = true
    · rw [List.filter_cons_of_pos hQ]
      by_cases hP : P x = true
      · rw [List.filter_cons_of_pos hP, List.filter_cons_of_pos hP, List.length_cons, List.length_cons]
        exact Nat.succ_le_succ ih
      · rw [List.filter_cons_of_neg hP, List.filter_cons_of_neg hP]
        exact ih
    · rw [List.filter_cons_of_neg hQ]
      by_cases hP : P x = true
      · rw [List.filter_cons_of_pos hP, List.length_cons]
        exact Nat.le_succ_of_le ih
      · rw [List.filter_cons_of_neg hP]
        exact ih

theorem epSquares_le8 (g : Cfg) (t : Nat) : (epSquares g t).length ≤ 8 := by
  rw [epSquares_eq]
  have h1 : (g.NK.filter fun s =>
        (rk s == (if g.col t = 0 then (5 : Int) else 2) &&
          !g.isK (sqOf (fl s) (rk s - pdir (g.col t))) &&
          !g.isK (sqOf (fl s) (rk s + pdir (g.col t))))).length ≤
      (g.NK.filter fun s => rk s == (if g.col t = 0 then (5 : Int) else 2)).length := by
    refine filter_length_le g.NK _ _ ?_
    intro a ha hb
    exact (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hb).1 |>.1
  have h2 : (g.NK.filter fun s => rk s == (if g.col t = 0 then (5 : Int) else 2)).length ≤
      ((List.range 64).filter fun s => rk s == (if g.col t = 0 then (5 : Int) else 2)).length :=
    filter_filter_length_le (List.range 64) _ (fun s => !g.isK s)
  have h8 : ((List.range 64).filter fun s => rk s == (5 : Int)).length = 8 ∧
      ((List.range 64).filter fun s => rk s == (2 : Int)).length = 8 := by decide
  have h3 : ((List.range 64).filter fun s => rk s == (if g.col t = 0 then (5 : Int) else 2)).length = 8 := by
    by_cases hh : g.col t = 0
    · rw [ite_eq_left hh]
      exact h8.1
    · rw [ite_eq_right hh]
      exact h8.2
  omega

theorem epCls_eq_none (g : Cfg) (t : Nat) (X0 : Array (List Int)) (E : List (Nat × Int)) :
    epCls g t X0 none E =
      (E.flatMap fun sv =>
        tag Fam.ep [[-sv.2, xv X0 (sqOf (fl sv.1) (rk sv.1 - pdir (g.col t)))
          (5 * (1 - g.col t) + P)], [-sv.2, xv X0 sv.1 EMP],
          [-sv.2, xv X0 (sqOf (fl sv.1) (rk sv.1 + pdir (g.col t))) EMP]]) ++
      tag Fam.ep (amoCls (E.map (·.2)) []) := rfl

theorem epCls_eq_some (g : Cfg) (t : Nat) (X0 : Array (List Int)) (q : Ply) (E : List (Nat × Int)) :
    epCls g t X0 (some q) E =
      (E.flatMap fun sv =>
        tag Fam.ep [[-sv.2, q.FR.getD (sqOf (fl sv.1) (rk sv.1 + pdir (g.col t))) 0],
          [-sv.2, q.TO.getD (sqOf (fl sv.1) (rk sv.1 - pdir (g.col t))) 0],
          [-sv.2, q.MP.getD P 0],
          [-q.FR.getD (sqOf (fl sv.1) (rk sv.1 + pdir (g.col t))) 0,
            -q.TO.getD (sqOf (fl sv.1) (rk sv.1 - pdir (g.col t))) 0, -q.MP.getD P 0, sv.2]]) ++ [] := rfl

theorem mem_epCls_none (g : Cfg) (t : Nat) (X0 : Array (List Int)) (E : List (Nat × Int))
    (c : Clause × Fam) (h : c ∈ epCls g t X0 none E) :
    (∃ sv ∈ E, c.1 = [-sv.2, xv X0 (sqOf (fl sv.1) (rk sv.1 - pdir (g.col t)))
        (5 * (1 - g.col t) + P)] ∨
      c.1 = [-sv.2, xv X0 sv.1 EMP] ∨
      c.1 = [-sv.2, xv X0 (sqOf (fl sv.1) (rk sv.1 + pdir (g.col t))) EMP]) ∨
    c.1 ∈ amoCls (E.map (·.2)) [] := by
  rw [epCls_eq_none] at h
  simp only [List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨sv, hsv, hc⟩ | hc
  · obtain ⟨-, hm⟩ := mem_tag _ Fam.ep _ hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact Or.inl ⟨sv, hsv, hm⟩
  · obtain ⟨-, hm⟩ := mem_tag _ Fam.ep _ hc
    exact Or.inr hm

theorem mem_epCls_some (g : Cfg) (t : Nat) (X0 : Array (List Int)) (q : Ply) (E : List (Nat × Int))
    (c : Clause × Fam) (h : c ∈ epCls g t X0 (some q) E) :
    ∃ sv ∈ E, c.1 = [-sv.2, q.FR.getD (sqOf (fl sv.1) (rk sv.1 + pdir (g.col t))) 0] ∨
      c.1 = [-sv.2, q.TO.getD (sqOf (fl sv.1) (rk sv.1 - pdir (g.col t))) 0] ∨
      c.1 = [-sv.2, q.MP.getD P 0] ∨
      c.1 = [-q.FR.getD (sqOf (fl sv.1) (rk sv.1 + pdir (g.col t))) 0,
        -q.TO.getD (sqOf (fl sv.1) (rk sv.1 - pdir (g.col t))) 0, -q.MP.getD P 0, sv.2] := by
  rw [epCls_eq_some] at h
  simp only [List.mem_flatMap, List.append_nil] at h
  obtain ⟨sv, hsv, hc⟩ := h
  obtain ⟨-, hm⟩ := mem_tag _ Fam.ep _ hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  exact ⟨sv, hsv, hm⟩

theorem mem_plyEprCls (g : Cfg) (t : Nat) (X0 X1 : Array (List Int)) (E : List (Nat × Int)) (q : Ply)
    (c : Clause × Fam) (h : c ∈ plyEprCls g t X0 X1 E q) :
    ∃ r gq srcs, (r, gq, srcs) ∈ eprSquares g t E ∧ ∃ v, look q.EPR r = some v ∧
      (c.1 = [-v, q.to gq] ∨ c.1 = [-v, q.mp P] ∨ c.1 = [-v, xv X0 r (5 * (1 - g.col t) + P)] ∨
        c.1 = [-v, (look E gq).getD 0] ∨ c.1 = [-v, xv X0 gq EMP] ∨ c.1 = -v :: srcs.map q.fr ∨
        c.1 = [-v, xv X1 r EMP]) := by
  unfold plyEprCls at h
  simp only [List.mem_flatMap] at h
  obtain ⟨⟨r, gq, srcs⟩, hmem, hc⟩ := h
  split at hc
  · rename_i hlo
    exact absurd hc List.not_mem_nil
  · rename_i v hlo
    obtain ⟨-, hm⟩ := mem_tag _ Fam.ep _ hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact ⟨r, gq, srcs, hmem, v, hlo, hm⟩

end X14

namespace X14b

theorem pawnMoves_promo_kindIdx (p : Pos) (s : Sq) (c0 : Color) (m : Move)
    (h : m ∈ pawnMoves p s c0) (k : Kind) (hp : m.promo = some k) : kindIdx k ≠ 0 := by
  unfold pawnMoves at h
  dsimp only at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨t, ht, hm⟩ := List.mem_flatMap.mp h
    by_cases hL : (t.rank == c0.last) = true
    · rw [ite_eq_left hL] at hm
      obtain ⟨k', hk', hkm⟩ := List.mem_map.mp hm
      have meq : m = ⟨s, t, some k'⟩ := hkm.symm
      have hkk : k' = k := by
        have hx : (⟨s, t, some k'⟩ : Move).promo = some k := meq ▸ hp
        exact Option.some.inj hx
      rw [← hkk]
      rcases List.mem_cons.mp hk' with h1 | hrest
      · rw [h1]; decide
      · rcases List.mem_cons.mp hrest with h2 | hrest
        · rw [h2]; decide
        · rcases List.mem_cons.mp hrest with h3 | hrest
          · rw [h3]; decide
          · rcases List.mem_cons.mp hrest with h4 | h5
            · rw [h4]; decide
            · simp at h5
    · rw [ite_eq_right hL] at hm
      rw [List.mem_singleton.mp hm] at hp
      cases hp
  · obtain ⟨t, ht, htm⟩ := List.mem_map.mp h
    rw [← htm] at hp
    have hn0 : (⟨s, t, none⟩ : Move).promo = none := rfl
    rw [hn0] at hp
    cases hp

theorem mem_plyCapCls (g : Cfg) (X0 : Array (List Int)) (q : Ply) (c : Clause × Fam)
    (h : c ∈ plyCapCls g X0 q) :
    (∃ h' ∈ g.NK, c.1 = [-q.to h', xv X0 h' EMP, q.CAP] ∨
      c.1 = [-q.CAP, -q.to h', -xv X0 h' EMP] ++ q.EPR.map (·.2)) ∨
    (∃ r v, (r, v) ∈ q.EPR ∧ c.1 = [-v, q.CAP]) := by
  unfold plyCapCls at h
  simp only [List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨h', hh', hc⟩ | hc
  · left
    exact ⟨h', hh', by
      obtain ⟨-, hm⟩ := mem_tag _ Fam.cap _ hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      exact hm⟩
  · obtain ⟨-, hm⟩ := mem_tag _ Fam.cap _ hc
    simp only [List.mem_map] at hm
    obtain ⟨v, hvin, he⟩ := hm
    obtain ⟨⟨r, vv⟩, hrv, hvv⟩ := hvin
    subst hvv
    exact Or.inr ⟨r, vv, hrv, he.symm⟩

theorem mem_plyPromoCls (g : Cfg) (t : Nat) (q : Ply) (c : Clause × Fam)
    (h : c ∈ plyPromoCls g t q) :
    c.1 = [-q.PROMO, q.mp P] ∨
    c.1 = -q.PROMO :: (g.NK.filter fun h' => rk h' == (if g.col t = 0 then (7 : Int) else 0)).map q.to ∨
    (∃ l ∈ (g.NK.filter fun h' => rk h' == (if g.col t = 0 then (7 : Int) else 0)).map q.to,
      c.1 = [-q.mp P, -l, q.PROMO]) ∨
    (∃ p0, p0 < 5 ∧ (c.1 = [q.PROMO, -q.mp p0, q.rt p0] ∨ c.1 = [q.PROMO, -q.rt p0, q.mp p0])) ∨
    c.1 = [-q.PROMO, -q.rt P] := by
  unfold plyPromoCls at h
  obtain ⟨-, hm⟩ := mem_tag _ Fam.promo _ h
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_flatMap, List.mem_range, or_assoc] at hm
  rcases hm with hm | hm | ⟨l, ⟨h', hh', hto⟩, hm⟩ | ⟨p0, hp0, hm⟩ | hm
  · exact Or.inl hm
  · exact Or.inr (Or.inl hm)
  · rw [← hto] at hm
    exact Or.inr (Or.inr (Or.inl ⟨q.to h', List.mem_map.mpr ⟨h', hh', rfl⟩, hm.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p0, hp0, hm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hm)))

theorem play_board_dst_none (p : Pos) (m : Move) (hp : m.promo = none) :
    (play p m).board m.dst = p.board m.src := by
  rw [play_board_dst, hp]

theorem play_board_dst_some (p : Pos) (m : Move) (k : Kind) (hp : m.promo = some k) :
    (play p m).board m.dst = (p.board m.src).map fun q => ⟨q.color, k⟩ := by
  rw [play_board_dst, hp]

theorem or3_false {a b c : Bool} (h : ((a || b) || c) = false) :
    a = false ∧ b = false ∧ c = false := by
  obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp h
  obtain ⟨h3, h4⟩ := Bool.or_eq_false_iff.mp h1
  exact ⟨h3, h4, h2⟩

theorem getD_toList {α : Type} (A : Array α) (i : Nat) (d : α) : A.toList.getD i d = A.getD i d := by
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList]

theorem take_cnt_map_sem (g : Cfg) (r : Run) (f : Nat → Sem) (v : Nat → Bool) (l : List Nat) (k : Nat)
    (h : ∀ s ∈ l, (f s).val g r = v s) :
    (((l.map f).take k).filter (fun a => a.val g r)).length =
      (((l.map v).take k).filter id).length := by
  induction l generalizing k with
  | nil => simp [List.map_nil, List.take_nil, List.filter]
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      have e1 := h x List.mem_cons_self
      have e2 := ih k (fun s hs => h s (List.mem_cons_of_mem _ hs))
      simp only [List.map_cons, List.take_succ_cons]
      cases hv : v x
      · rw [hv] at e1
        have hn0 : ¬Sem.val g r (f x) = true := by rw [e1]; decide
        rw [List.filter_cons_of_neg hn0, List.filter_cons_of_neg (by decide)]
        exact e2
      · rw [hv] at e1
        have hp0 : (fun a => Sem.val g r a) (f x) = true := e1
        rw [List.filter_cons_of_pos hp0, List.filter_cons_of_pos (by decide),
          List.length_cons, List.length_cons, e2]

theorem caps_eq_cnt (p : Pos) (ms : List Move) :
    caps p ms = (((List.range ms.length).map
      fun t => isCapture (after p (ms.take t)) (ms.getD t default)).filter id).length := by
  induction ms generalizing p with
  | nil => rfl
  | cons m0 ms0 ih =>
    show (if isCapture p m0 = true then 1 else 0) + caps (play p m0) ms0 = _
    rw [List.length_cons, List.range_succ_eq_map]
    show _ = (((0 :: (List.range ms0.length).map fun i => i + 1).map
      fun t => isCapture (after p ((m0 :: ms0).take t)) ((m0 :: ms0).getD t default)).filter id).length
    rw [List.map_cons, List.map_map, ih (play p m0)]
    have hf : ((fun t => isCapture (after p ((m0 :: ms0).take t)) ((m0 :: ms0).getD t default)) ∘
        (fun i => i + 1)) =
        (fun t => isCapture (after (play p m0) (ms0.take t)) (ms0.getD t default)) := by
      funext t
      show isCapture (after p ((m0 :: ms0).take (t + 1))) ((m0 :: ms0).getD (t + 1) default) = _
      rw [List.getD_cons_succ]
      rfl
    rw [hf]
    show _ = ((isCapture p m0 ::
        ((List.range ms0.length).map
          fun t => isCapture (after (play p m0) (ms0.take t)) (ms0.getD t default))).filter id).length
    cases hc : isCapture p m0
    · rw [if_neg (by decide), List.filter_cons_of_neg (by decide), Nat.zero_add]
    · rw [if_pos rfl, List.filter_cons_of_pos (by decide), List.length_cons, Nat.add_comm 1]

theorem S_empty' (g : Cfg) (h1 : 1 ≤ g.n) (hm : g.m = 0) : (encodeCfg g).layout.S.toList = [] := by
  obtain ⟨XXL, AT, e0, EP, a1, a2, ae, aP, h1', h2', he', hp', hs', hpl⟩ := X6.decomp g
  obtain ⟨L0v, aL, hA⟩ : ∃ L0v aL, (amoAlloc (X6.attRolesOf AT 0 0)).run aP = (L0v, aL) := ⟨_, _, rfl⟩
  obtain ⟨LSv, aLS, hLS⟩ : ∃ LSv aLS, (X6.lsLoop g AT).run aL = (LSv, aLS) := ⟨_, _, rfl⟩
  have htg := X6.tail_eq_ge g XXL AT EP h1
  have hS : (encodeCfg g).layout.S =
      (((counterAlloc g (EP.2.toList.map (·.CAP))).run ((X6.lsLoop g AT).run aL).2).1).toArray := by
    rw [X6.encodeCfg_layout, X6.layoutM_eq]
    simp only [run_bind]
    rw [h1', h2', he', hp', htg]
    simp only [run_bind]
    rw [hA, X6.rest_S, hLS]
  rw [hS]
  unfold counterAlloc
  rw [ite_eq_left hm]
  rw [run_pure]

end X14b

theorem fam_ep : FamOK w b n m .ep := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_append, List.mem_flatMap, List.mem_range] at hfm
  rcases hfm with h0 | ⟨t, ht, hepr | hepc⟩
  · have hturn0 : p.turn = .white := hch.2.1
    unfold ep0Part at h0
    rcases X14.mem_epCls_none (cfgOf w b n m) 0 _ _ _ h0 with ⟨sv, hsv, hcl⟩ | hamo
    · have hrole := (roles_eps (cfgOf w b n m) 0 (Nat.zero_le n)).2 sv hsv
      have hev : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) sv.2 =
          (((runOf p ms).pos 0).ep == some (toSq sv.1)) := lit_pos _ _ _ _ hrole
      have hzv : sv.2 ≠ 0 := by
        have h0v : 0 < sv.2 := hrole.1
        omega
      have hpos0 : (runOf p ms).pos 0 = p := rfl
      have hcol0 : (cfgOf w b n m).col 0 = 0 := rfl
      have hpd0 : pdir ((cfgOf w b n m).col 0) = 1 := rfl
      have hsEp : sv.1 ∈ epSquares (cfgOf w b n m) 0 := by
        have hmap : ((encodeCfg (cfgOf w b n m)).layout.EPS.getD 0 []).map (fun x => x.1) =
            epSquares (cfgOf w b n m) 0 := (roles_eps (cfgOf w b n m) 0 (Nat.zero_le n)).1
        rw [← hmap]
        exact List.mem_map.mpr ⟨sv, hsv, rfl⟩
      rw [epSquares_eq] at hsEp
      obtain ⟨hsNK, hcond⟩ := List.mem_filter.mp hsEp
      rw [hcol0, ite_eq_left (rfl : (0 : Nat) = 0)] at hcond
      have hcA := (Bool.and_eq_true _ _).mp hcond
      have hcd2 := (Bool.and_eq_true _ _).mp hcA.1
      have hr5 : rk sv.1 = 5 := beq_iff_eq.mp hcd2.1
      have hs64 : sv.1 < 64 := List.mem_range.mp (List.mem_filter.mp hsNK).1
      have honbm : onb (fl sv.1) (rk sv.1 - 1) = true := by
        have b1 : (0 : Int) ≤ fl sv.1 ∧ fl sv.1 < 8 := by
          have e : fl sv.1 = ((sv.1 % 8 : Nat) : Int) := rfl
          omega
        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
        omega
      have honbp : onb (fl sv.1) (rk sv.1 + 1) = true := by
        have b1 : (0 : Int) ≤ fl sv.1 ∧ fl sv.1 < 8 := by
          have e : fl sv.1 = ((sv.1 % 8 : Nat) : Int) := rfl
          omega
        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
        omega
      obtain ⟨h64m, -, -⟩ := onb_sqOf _ _ honbm
      obtain ⟨h64p, -, -⟩ := onb_sqOf _ _ honbp
      have honbm2 : onb (fl sv.1) (rk sv.1 - pdir ((cfgOf w b n m).col 0)) = true := by
        rw [hpd0]
        exact honbm
      have honbp2 : onb (fl sv.1) (rk sv.1 + pdir ((cfgOf w b n m).col 0)) = true := by
        rw [hpd0]
        exact honbp
      have hdmNK : sqOf (fl sv.1) (rk sv.1 - pdir ((cfgOf w b n m).col 0)) ∈ (cfgOf w b n m).NK := by
        rw [hpd0]
        exact List.mem_filter.mpr ⟨List.mem_range.mpr h64m, hcd2.2⟩
      have hdpNK : sqOf (fl sv.1) (rk sv.1 + pdir ((cfgOf w b n m).col 0)) ∈ (cfgOf w b n m).NK := by
        rw [hpd0]
        exact List.mem_filter.mpr ⟨List.mem_range.mpr h64p, hcA.2⟩
      have hkindex : 5 * (1 - (cfgOf w b n m).col 0) + P < 11 := by
        rw [hcol0]
        decide
      have hEMP11 : EMP < 11 := by decide
      rcases hcl with hcl | hcl | hcl
      · rw [hcl]
        cases hevb : (((runOf p ms).pos 0).ep == some (toSq sv.1))
        · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hevb]; rfl)
        · have hs' : ((runOf p ms).pos 0).ep = some (toSq sv.1) := beq_iff_eq.mp hevb
          obtain ⟨-, hep0⟩ := core_ep0 hch (toSq sv.1) hs'
          obtain ⟨hr5o, hsn, ⟨o, hoffo, hon⟩, ⟨d, hoffd, hdb⟩⟩ := hep0
          obtain ⟨hfxd, hryd⟩ := (off_eq_some (toSq sv.1) d 0 (-p.turn.fwd)).mp hoffd
          have hfw : p.turn.fwd = 1 := by rw [hturn0]; decide
          have hfxd2 : fx d = fl sv.1 := by
            have e1 := fx_toSq sv.1 hs64
            omega
          have hryd2 : ry d = rk sv.1 - pdir ((cfgOf w b n m).col 0) := by
            rw [hpd0]
            have e2 := ry_toSq sv.1 hs64
            omega
          have hdts : toSq (sqOf (fl sv.1) (rk sv.1 - pdir ((cfgOf w b n m).col 0))) = d :=
            toSq_sqOf_eq d _ _ honbm2 hfxd2 hryd2
          have hexD : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
              (xv ((encodeCfg (cfgOf w b n m)).layout.X0 0)
                (sqOf (fl sv.1) (rk sv.1 - pdir ((cfgOf w b n m).col 0)))
                (5 * (1 - (cfgOf w b n m).col 0) + P)) =
              (code (((runOf p ms).pos 0).board
                (toSq (sqOf (fl sv.1) (rk sv.1 - pdir ((cfgOf w b n m).col 0))))) ==
                (5 * (1 - (cfgOf w b n m).col 0) + P)) :=
            lit_pos _ _ _ _ (roles_X (cfgOf w b n m) 0
              (sqOf (fl sv.1) (rk sv.1 - pdir ((cfgOf w b n m).col 0))) _
              (Nat.zero_le n) hdmNK hkindex)
          exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [hexD, hdts, hdb, hpos0, hturn0, hcol0]; decide)
      · rw [hcl]
        cases hevb : (((runOf p ms).pos 0).ep == some (toSq sv.1))
        · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hevb]; rfl)
        · have hs' : ((runOf p ms).pos 0).ep = some (toSq sv.1) := beq_iff_eq.mp hevb
          obtain ⟨-, hep0⟩ := core_ep0 hch (toSq sv.1) hs'
          obtain ⟨hr5o, hsn, -, -⟩ := hep0
          have hexS : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
              (xv ((encodeCfg (cfgOf w b n m)).layout.X0 0) sv.1 EMP) =
              (code (((runOf p ms).pos 0).board (toSq sv.1)) == EMP) :=
            lit_pos _ _ _ _ (roles_X (cfgOf w b n m) 0 sv.1 EMP (Nat.zero_le n) hsNK hEMP11)
          exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [hexS, hsn]; decide)
      · rw [hcl]
        cases hevb : (((runOf p ms).pos 0).ep == some (toSq sv.1))
        · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hevb]; rfl)
        · have hs' : ((runOf p ms).pos 0).ep = some (toSq sv.1) := beq_iff_eq.mp hevb
          obtain ⟨-, hep0⟩ := core_ep0 hch (toSq sv.1) hs'
          obtain ⟨hr5o, hsn, ⟨o, hoffo, hon⟩, -⟩ := hep0
          obtain ⟨hfxo, hryo⟩ := (off_eq_some (toSq sv.1) o 0 p.turn.fwd).mp hoffo
          have hfw : p.turn.fwd = 1 := by rw [hturn0]; decide
          have hfxo2 : fx o = fl sv.1 := by
            have e1 := fx_toSq sv.1 hs64
            omega
          have hryo2 : ry o = rk sv.1 + pdir ((cfgOf w b n m).col 0) := by
            rw [hpd0]
            have e2 := ry_toSq sv.1 hs64
            omega
          have hots : toSq (sqOf (fl sv.1) (rk sv.1 + pdir ((cfgOf w b n m).col 0))) = o :=
            toSq_sqOf_eq o _ _ honbp2 hfxo2 hryo2
          have hexO : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
              (xv ((encodeCfg (cfgOf w b n m)).layout.X0 0)
                (sqOf (fl sv.1) (rk sv.1 + pdir ((cfgOf w b n m).col 0))) EMP) =
              (code (((runOf p ms).pos 0).board
                (toSq (sqOf (fl sv.1) (rk sv.1 + pdir ((cfgOf w b n m).col 0))))) == EMP) :=
            lit_pos _ _ _ _ (roles_X (cfgOf w b n m) 0
              (sqOf (fl sv.1) (rk sv.1 + pdir ((cfgOf w b n m).col 0))) EMP (Nat.zero_le n) hdpNK hEMP11)
          exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [hexO, hots, hon]; decide)
    · have hlt8 : (((encodeCfg (cfgOf w b n m)).layout.EPS.getD 0 []).map (fun x => x.2)).length ≤ 8 := by
        have hle : (((encodeCfg (cfgOf w b n m)).layout.EPS.getD 0 []).map (fun x => x.2)).length =
            (epSquares (cfgOf w b n m) 0).length := by
          have hmap := (roles_eps (cfgOf w b n m) 0 (Nat.zero_le n)).1
          calc (((encodeCfg (cfgOf w b n m)).layout.EPS.getD 0 []).map fun x => x.2).length
              = ((encodeCfg (cfgOf w b n m)).layout.EPS.getD 0 []).length := by rw [List.length_map]
            _ = (((encodeCfg (cfgOf w b n m)).layout.EPS.getD 0 []).map fun x => x.1).length := by
              rw [List.length_map]
            _ = (epSquares (cfgOf w b n m) 0).length := congrArg List.length hmap
        rw [hle]
        exact X14.epSquares_le8 (cfgOf w b n m) 0
      exact amo_sound _ _ [] _ (fun l hl => by
          obtain ⟨sv, hsv2, rfl⟩ := List.mem_map.mp hl
          have h0v : 0 < sv.2 := ((roles_eps (cfgOf w b n m) 0 (Nat.zero_le n)).2 _ hsv2).1
          omega)
        (fun l hl => by simp at hl)
        (X13.fa2_map_of _ _ _ _ fun sv hsv2 =>
          lit_pos _ _ _ _ ((roles_eps (cfgOf w b n m) 0 (Nat.zero_le n)).2 _ hsv2))
        (X14.cnt_eps_le1 ((runOf p ms).pos 0).ep _ (by
          rw [(roles_eps (cfgOf w b n m) 0 (Nat.zero_le n)).1]
          show ((cfgOf w b n m).NK.filter _).Nodup
          exact List.Pairwise.filter _ (List.Pairwise.filter _ List.nodup_range))
        (fun sv hsv2 => by
          have hmem : sv.1 ∈ epSquares (cfgOf w b n m) 0 := by
            have hmap := (roles_eps (cfgOf w b n m) 0 (Nat.zero_le n)).1
            rw [← hmap]
            exact List.mem_map.mpr ⟨sv, hsv2, rfl⟩
          exact List.mem_range.mp (List.mem_filter.mp (List.mem_filter.mp hmem).1).1))
        (fun h8 => absurd h8 (by omega)) c.1 hamo
  · obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
    obtain ⟨rX, gq, srcs, heprm, v, hlook, hcl⟩ :=
      X14.mem_plyEprCls (cfgOf w b n m) t _ _ _ _ c hepr
    rw [eprSquares_eq] at heprm
    obtain ⟨rX0, hrNKX0, hval⟩ := List.mem_filterMap.mp heprm
    cases hbb : (rk rX0 != (if (cfgOf w b n m).col t = 0 then (4 : Int) else 3))
    · rw [if_neg (fun hh => by rw [hbb] at hh; cases hh)] at hval
      cases hlkv : look ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t [])
          (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t))) with
      | none =>
          rw [if_pos (by rw [hlkv]; rfl)] at hval
          cases hval
      | some epsv =>
          have isnn : Option.isNone (look ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t [])
              (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)))) = false := by
            rw [hlkv]
            rfl
          rw [if_neg (fun hh => by rw [isnn] at hh; cases hh)] at hval
          split at hval
          · rename_i hem
            cases hval
          · rename_i hem
            simp only [Option.some.injEq, Prod.mk.injEq] at hval
            obtain ⟨rfl, rfl, rfl⟩ := hval
            have hrr : rk rX0 = (if (cfgOf w b n m).col t = 0 then (4 : Int) else 3) :=
              bne_eq_false_iff_eq.mp hbb
            have hrNK : rX0 ∈ (cfgOf w b n m).NK := hrNKX0
            have hrolev := (roles_EPR (cfgOf w b n m) t ht).2 _ (X13.mem_of_look hlook)
            have hev : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) v =
                (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq rX0)) := lit_pos _ _ _ _ hrolev
            have hzv : v ≠ 0 := by
              have h0v : 0 < v := hrolev.1
              omega
            have hturn := run_turn hch t (Nat.le_of_lt ht)
            have hr64 : rX0 < 64 := List.mem_range.mp (List.mem_filter.mp hrNK).1
            cases hvicB : (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq rX0))
            · rcases hcl with hcl | hcl | hcl | hcl | hcl | hcl | hcl
              · rw [hcl]
                exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hvicB]; rfl)
              · rw [hcl]
                exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hvicB]; rfl)
              · rw [hcl]
                exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hvicB]; rfl)
              · rw [hcl]
                exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hvicB]; rfl)
              · rw [hcl]
                exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hvicB]; rfl)
              · rw [hcl]
                exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hvicB]; rfl)
              · rw [hcl]
                exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hvicB]; rfl)
            · have hvic : epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some (toSq rX0) := beq_iff_eq.mp hvicB
              obtain ⟨hep, hdn0, hvb, hfxv, hryv, hsrcb⟩ := epVictim_spec _ _ _ hleg hvic
              obtain ⟨hkw2, hkb2, -⟩ := run_kings hch t (Nat.le_of_lt ht)
              obtain ⟨q, hqsrc, hqcol, hpiece⟩ := legal_nonking_mem _ _ hleg hkm
              have hqs : q = ⟨(((runOf p ms).pos t)).turn, .pawn⟩ := Option.some.inj (hqsrc.symm.trans hsrcb)
              subst hqs
              have hpm : ((runOf p ms).mv t) ∈ pawnMoves ((runOf p ms).pos t) ((runOf p ms).mv t).src (((runOf p ms).pos t)).turn := hpiece
              obtain ⟨-, hdisj, -⟩ := pawnMoves_cases _ _ _ _ hpm
              have hfnI : fx ((runOf p ms).mv t).src ≠ fx ((runOf p ms).mv t).dst := by
                rw [epVictim_eq] at hvic
                by_cases hcc : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn) &&
                    ((runOf p ms).mv t).src.file != ((runOf p ms).mv t).dst.file && empty ((runOf p ms).pos t).board ((runOf p ms).mv t).dst) = true
                · rw [if_pos hcc] at hvic
                  have hfn : ((runOf p ms).mv t).src.file ≠ ((runOf p ms).mv t).dst.file :=
                    bne_iff_ne.mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hcc).1).2
                  intro he
                  exact hfn (Int.ofNat_inj.mp he)
                · rw [if_neg hcc] at hvic
                  cases hvic
              rcases hdisj with hd1 | hd2 | hd3
              · exact absurd hd1.1.symm hfnI
              · exact absurd hd2.1.symm hfnI
              · obtain ⟨hatt, -⟩ := hd3
                obtain ⟨hry3, hfx3⟩ := pawn_attack_geom _ _ _ _ hatt
                have hdf2 : fx ((runOf p ms).mv t).dst - fx ((runOf p ms).mv t).src = 1 ∨ fx ((runOf p ms).mv t).dst - fx ((runOf p ms).mv t).src = -1 := by omega
                have hnokS' : ∀ cc, ((runOf p ms).pos t).board (toSq ((runOf p ms).mv t).src.val) ≠ some ⟨cc, .king⟩ := by
                  intro cc hh
                  rw [toSq_val, hsrcb] at hh
                  have hk2 := congrArg (fun (x : Piece) => x.kind) (Option.some.inj hh)
                  have hk3 : Kind.pawn = Kind.king := hk2
                  cases hk3
                rcases color_parity (t % 2) (Nat.mod_lt _ (by decide)) with ⟨he, hcol, hpd, hfw, hh⟩ |
                  ⟨he, hcol, hpd, hfw, hh⟩
                · have hcole : (cfgOf w b n m).col t = 0 := he
                  have htc : ((runOf p ms).pos t).turn = .white := hturn.trans hcol
                  have hrrC : rk rX0 = 4 := by
                    rw [hcole, ite_eq_left (rfl : (0 : Nat) = 0)] at hrr
                    exact hrr
                  have hpdx : pdir ((cfgOf w b n m).col t) = (1 : Int) := by rw [hcole]; rfl
                  have hfwC : ((runOf p ms).pos t).turn.fwd = (1 : Int) := by rw [htc]; decide
                  have hbx : 5 * (1 - (cfgOf w b n m).col t) + P < 11 := by rw [hcole]; decide
                  have hfld : fx ((runOf p ms).mv t).dst = fl rX0 := by
                    have e1 := fx_toSq rX0 hr64
                    omega
                  have hrydst : ry ((runOf p ms).mv t).dst = rk rX0 + pdir ((cfgOf w b n m).col t) := by
                    rw [hpdx]
                    have e2 := ry_toSq rX0 hr64
                    omega
                  have honbG : onb (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)) = true := by
                    rw [hpdx]
                    simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
                    have efl : fl rX0 = ((rX0 % 8 : Nat) : Int) := rfl
                    omega
                  obtain ⟨h64G, hflG, hrkG⟩ := onb_sqOf _ _ honbG
                  have hdstT : toSq (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t))) = ((runOf p ms).mv t).dst := by
                    refine toSq_sqOf_eq _ _ _ honbG ?_ ?_
                    · have e1 := fx_toSq rX0 hr64
                      omega
                    · exact hrydst
                  have hdval : ((runOf p ms).mv t).dst.val = sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)) := by
                    have hd1 : (toSq (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)))).val =
                        sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)) := Nat.mod_eq_of_lt h64G
                    rw [hdstT] at hd1
                    exact hd1
                  have hnkG : sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)) ∈ (cfgOf w b n m).NK := by
                    have hmem : sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)) ∈ epSquares (cfgOf w b n m) t := by
                      have hmap := (roles_eps (cfgOf w b n m) t (Nat.le_of_lt ht)).1
                      rw [← hmap]
                      exact List.mem_map.mpr ⟨(sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)), epsv),
                        X13.mem_of_look hlkv, rfl⟩
                    exact (List.mem_filter.mp hmem).1
                  have hetoG : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).to (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)))) =
                      (((runOf p ms).mv t).dst.val == (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)))) :=
                    lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t _ ht hnkG).2
                  have hespE : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) epsv = ((((runOf p ms).pos t)).ep == some (toSq (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t))))) :=
                    lit_pos _ _ _ _ ((roles_eps (cfgOf w b n m) t (Nat.le_of_lt ht)).2 _ (X13.mem_of_look hlkv))
                  have hexMP : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).mp P) = ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn)) :=
                    (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 P (by decide)).1).trans
                      (X14.any_kindIdx_pawn _)
                  have hex0r : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) rX0 (5 * (1 - (cfgOf w b n m).col t) + P)) =
                      (code ((((runOf p ms).pos t)).board (toSq rX0)) == (5 * (1 - (cfgOf w b n m).col t) + P)) :=
                    lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t rX0 _ (Nat.le_of_lt ht) hrNK hbx)
                  have hex0G : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t))) EMP) =
                      (code ((((runOf p ms).pos t)).board (toSq (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t))))) == EMP) :=
                    lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t _ EMP (Nat.le_of_lt ht) hnkG (by decide))
                  have hex1r : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (xv ((encodeCfg (cfgOf w b n m)).layout.X0 (t + 1)) rX0 EMP) =
                      (code (((runOf p ms).pos (t + 1)).board (toSq rX0)) == EMP) :=
                    lit_pos _ _ _ _ (roles_X (cfgOf w b n m) (t + 1) rX0 EMP (by omega) hrNK (by decide))
                  have hvbC : (((runOf p ms).pos t)).board (toSq rX0) = some ⟨.black, .pawn⟩ := by
                    rw [htc] at hvb
                    exact hvb
                  have hnedst : toSq rX0 ≠ ((runOf p ms).mv t).dst := by
                    intro e
                    have e1 := congrArg ry e
                    have e2 := ry_toSq rX0 hr64
                    omega
                  have hbad1 : ((runOf p ms).pos (t + 1)).board (toSq rX0) = none := by
                    rw [hstep]
                    exact play_board_epVictim _ _ _ hvic hnedst
                  have hSrcNK : ((runOf p ms).mv t).src.val ∈ (cfgOf w b n m).NK := by
                    have hib : (cfgOf w b n m).isK ((runOf p ms).mv t).src.val = false :=
                      isK_false_of_noking _ _ hkw2 hkb2 hnokS'
                    exact List.mem_filter.mpr ⟨List.mem_range.mpr ((runOf p ms).mv t).src.isLt, by rw [hib]; rfl⟩
                  have hefrS2 : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).fr ((runOf p ms).mv t).src.val) = (((runOf p ms).mv t).src.val == ((runOf p ms).mv t).src.val) :=
                    lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t ((runOf p ms).mv t).src.val ht hSrcNK).1
                  have hsrce : ((runOf p ms).mv t).src.val ∈ [-1, 1].filterMap fun df => if onb (fl rX0 + df) (rk rX0) && !(cfgOf w b n m).isK (sqOf (fl rX0 + df) (rk rX0)) then some (sqOf (fl rX0 + df) (rk rX0)) else none := by
                    refine List.mem_filterMap.mpr ⟨fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst, ?_, ?_⟩
                    · rcases hdf2 with hdF | hdF
                      · rw [show fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst = (-1 : Int) by omega]
                        decide
                      · rw [show fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst = (1 : Int) by omega]
                        decide
                    · have efl : fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst) = fl ((runOf p ms).mv t).src.val := by
                        have e1 := fx_toSq rX0 hr64
                        have e2 : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
                        omega
                      have erk : rk rX0 = rk ((runOf p ms).mv t).src.val := by
                        have e1 := ry_toSq rX0 hr64
                        have e2 : rk ((runOf p ms).mv t).src.val = ry ((runOf p ms).mv t).src := rfl
                        omega
                      have conb : onb (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0) = true := by
                        rw [efl, erk]
                        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
                        have b1 := fx_nonneg ((runOf p ms).mv t).src
                        have b2 := fx_lt ((runOf p ms).mv t).src
                        have lf : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
                        have lr : rk ((runOf p ms).mv t).src.val = ry ((runOf p ms).mv t).src := rfl
                        have e2 := ry_toSq rX0 hr64
                        omega
                      have cisk : (!(cfgOf w b n m).isK (sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0))) = true := by
                        have hsqeq : sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0) = ((runOf p ms).mv t).src.val := by
                          calc sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0) = sqOf (fl ((runOf p ms).mv t).src.val) (rk ((runOf p ms).mv t).src.val) := by
                                rw [efl, erk]
                            _ = ((runOf p ms).mv t).src.val := fl_rk_sqOf _
                        rw [hsqeq, isK_false_of_noking _ _ hkw2 hkb2 hnokS']
                        rfl
                      show (if onb (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0) &&
                          !(cfgOf w b n m).isK (sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0)) then
                          some (sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0)) else none) = some ((runOf p ms).mv t).src.val
                      rw [if_pos ((Bool.and_eq_true _ _).mpr ⟨conb, cisk⟩)]
                      exact congrArg some (by
                        calc sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0) = sqOf (fl ((runOf p ms).mv t).src.val) (rk ((runOf p ms).mv t).src.val) := by
                              rw [efl, erk]
                          _ = ((runOf p ms).mv t).src.val := fl_rk_sqOf _)
                  rcases hcl with hcl | hcl | hcl | hcl | hcl | hcl | hcl
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hetoG]; exact beq_iff_eq.mpr hdval)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hexMP, hsrcb]; rfl)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hex0r, hvbC, hcole]; decide)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hlkv, Option.getD_some, hespE, hep, ← hdstT]; exact beq_self_eq_true _)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hex0G, hdstT, hdn0]; decide)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨((runOf p ms).mv t).src.val, hsrce, rfl⟩))
                      (by rw [hefrS2]; exact beq_self_eq_true _)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hex1r, hbad1]; decide)
                · have hcole : (cfgOf w b n m).col t = 1 := he
                  have htc : ((runOf p ms).pos t).turn = .black := hturn.trans hcol
                  have hrrC : rk rX0 = 3 := by
                    rw [hcole, ite_eq_right (by decide)] at hrr
                    exact hrr
                  have hpdx : pdir ((cfgOf w b n m).col t) = (-1 : Int) := by rw [hcole]; rfl
                  have hfwC : ((runOf p ms).pos t).turn.fwd = (-1 : Int) := by rw [htc]; decide
                  have hbx : 5 * (1 - (cfgOf w b n m).col t) + P < 11 := by rw [hcole]; decide
                  have hfld : fx ((runOf p ms).mv t).dst = fl rX0 := by
                    have e1 := fx_toSq rX0 hr64
                    omega
                  have hrydst : ry ((runOf p ms).mv t).dst = rk rX0 + pdir ((cfgOf w b n m).col t) := by
                    rw [hpdx]
                    have e2 := ry_toSq rX0 hr64
                    omega
                  have honbG : onb (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)) = true := by
                    rw [hpdx]
                    simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
                    have efl : fl rX0 = ((rX0 % 8 : Nat) : Int) := rfl
                    omega
                  obtain ⟨h64G, hflG, hrkG⟩ := onb_sqOf _ _ honbG
                  have hdstT : toSq (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t))) = ((runOf p ms).mv t).dst := by
                    refine toSq_sqOf_eq _ _ _ honbG ?_ ?_
                    · have e1 := fx_toSq rX0 hr64
                      omega
                    · exact hrydst
                  have hdval : ((runOf p ms).mv t).dst.val = sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)) := by
                    have hd1 : (toSq (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)))).val =
                        sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)) := Nat.mod_eq_of_lt h64G
                    rw [hdstT] at hd1
                    exact hd1
                  have hnkG : sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)) ∈ (cfgOf w b n m).NK := by
                    have hmem : sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)) ∈ epSquares (cfgOf w b n m) t := by
                      have hmap := (roles_eps (cfgOf w b n m) t (Nat.le_of_lt ht)).1
                      rw [← hmap]
                      exact List.mem_map.mpr ⟨(sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)), epsv),
                        X13.mem_of_look hlkv, rfl⟩
                    exact (List.mem_filter.mp hmem).1
                  have hetoG : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).to (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)))) =
                      (((runOf p ms).mv t).dst.val == (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t)))) :=
                    lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t _ ht hnkG).2
                  have hespE : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) epsv = ((((runOf p ms).pos t)).ep == some (toSq (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t))))) :=
                    lit_pos _ _ _ _ ((roles_eps (cfgOf w b n m) t (Nat.le_of_lt ht)).2 _ (X13.mem_of_look hlkv))
                  have hexMP : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).mp P) = ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn)) :=
                    (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 P (by decide)).1).trans
                      (X14.any_kindIdx_pawn _)
                  have hex0r : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) rX0 (5 * (1 - (cfgOf w b n m).col t) + P)) =
                      (code ((((runOf p ms).pos t)).board (toSq rX0)) == (5 * (1 - (cfgOf w b n m).col t) + P)) :=
                    lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t rX0 _ (Nat.le_of_lt ht) hrNK hbx)
                  have hex0G : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t))) EMP) =
                      (code ((((runOf p ms).pos t)).board (toSq (sqOf (fl rX0) (rk rX0 + pdir ((cfgOf w b n m).col t))))) == EMP) :=
                    lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t _ EMP (Nat.le_of_lt ht) hnkG (by decide))
                  have hex1r : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (xv ((encodeCfg (cfgOf w b n m)).layout.X0 (t + 1)) rX0 EMP) =
                      (code (((runOf p ms).pos (t + 1)).board (toSq rX0)) == EMP) :=
                    lit_pos _ _ _ _ (roles_X (cfgOf w b n m) (t + 1) rX0 EMP (by omega) hrNK (by decide))
                  have hvbC : (((runOf p ms).pos t)).board (toSq rX0) = some ⟨.white, .pawn⟩ := by
                    rw [htc] at hvb
                    exact hvb
                  have hnedst : toSq rX0 ≠ ((runOf p ms).mv t).dst := by
                    intro e
                    have e1 := congrArg ry e
                    have e2 := ry_toSq rX0 hr64
                    omega
                  have hbad1 : ((runOf p ms).pos (t + 1)).board (toSq rX0) = none := by
                    rw [hstep]
                    exact play_board_epVictim _ _ _ hvic hnedst
                  have hSrcNK : ((runOf p ms).mv t).src.val ∈ (cfgOf w b n m).NK := by
                    have hib : (cfgOf w b n m).isK ((runOf p ms).mv t).src.val = false :=
                      isK_false_of_noking _ _ hkw2 hkb2 hnokS'
                    exact List.mem_filter.mpr ⟨List.mem_range.mpr ((runOf p ms).mv t).src.isLt, by rw [hib]; rfl⟩
                  have hefrS2 : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).fr ((runOf p ms).mv t).src.val) = (((runOf p ms).mv t).src.val == ((runOf p ms).mv t).src.val) :=
                    lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t ((runOf p ms).mv t).src.val ht hSrcNK).1
                  have hsrce : ((runOf p ms).mv t).src.val ∈ [-1, 1].filterMap fun df => if onb (fl rX0 + df) (rk rX0) && !(cfgOf w b n m).isK (sqOf (fl rX0 + df) (rk rX0)) then some (sqOf (fl rX0 + df) (rk rX0)) else none := by
                    refine List.mem_filterMap.mpr ⟨fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst, ?_, ?_⟩
                    · rcases hdf2 with hdF | hdF
                      · rw [show fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst = (-1 : Int) by omega]
                        decide
                      · rw [show fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst = (1 : Int) by omega]
                        decide
                    · have efl : fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst) = fl ((runOf p ms).mv t).src.val := by
                        have e1 := fx_toSq rX0 hr64
                        have e2 : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
                        omega
                      have erk : rk rX0 = rk ((runOf p ms).mv t).src.val := by
                        have e1 := ry_toSq rX0 hr64
                        have e2 : rk ((runOf p ms).mv t).src.val = ry ((runOf p ms).mv t).src := rfl
                        omega
                      have conb : onb (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0) = true := by
                        rw [efl, erk]
                        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
                        have b1 := fx_nonneg ((runOf p ms).mv t).src
                        have b2 := fx_lt ((runOf p ms).mv t).src
                        have lf : fl ((runOf p ms).mv t).src.val = fx ((runOf p ms).mv t).src := rfl
                        have lr : rk ((runOf p ms).mv t).src.val = ry ((runOf p ms).mv t).src := rfl
                        have e2 := ry_toSq rX0 hr64
                        omega
                      have cisk : (!(cfgOf w b n m).isK (sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0))) = true := by
                        have hsqeq : sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0) = ((runOf p ms).mv t).src.val := by
                          calc sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0) = sqOf (fl ((runOf p ms).mv t).src.val) (rk ((runOf p ms).mv t).src.val) := by
                                rw [efl, erk]
                            _ = ((runOf p ms).mv t).src.val := fl_rk_sqOf _
                        rw [hsqeq, isK_false_of_noking _ _ hkw2 hkb2 hnokS']
                        rfl
                      show (if onb (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0) &&
                          !(cfgOf w b n m).isK (sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0)) then
                          some (sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0)) else none) = some ((runOf p ms).mv t).src.val
                      rw [if_pos ((Bool.and_eq_true _ _).mpr ⟨conb, cisk⟩)]
                      exact congrArg some (by
                        calc sqOf (fl rX0 + (fx ((runOf p ms).mv t).src - fx ((runOf p ms).mv t).dst)) (rk rX0) = sqOf (fl ((runOf p ms).mv t).src.val) (rk ((runOf p ms).mv t).src.val) := by
                              rw [efl, erk]
                          _ = ((runOf p ms).mv t).src.val := fl_rk_sqOf _)
                  rcases hcl with hcl | hcl | hcl | hcl | hcl | hcl | hcl
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hetoG]; exact beq_iff_eq.mpr hdval)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hexMP, hsrcb]; rfl)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hex0r, hvbC, hcole]; decide)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hlkv, Option.getD_some, hespE, hep, ← hdstT]; exact beq_self_eq_true _)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hex0G, hdstT, hdn0]; decide)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨((runOf p ms).mv t).src.val, hsrce, rfl⟩))
                      (by rw [hefrS2]; exact beq_self_eq_true _)
                  · rw [hcl]
                    exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                      (by rw [hex1r, hbad1]; decide)
    · rw [if_pos hbb] at hval
      cases hval
  · obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
    obtain ⟨sv, hsv, hcl⟩ := X14.mem_epCls_some (cfgOf w b n m) (t + 1) _ _ _ _ hepc
    have hrole := (roles_eps (cfgOf w b n m) (t + 1) (by omega)).2 sv hsv
    have hev : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) sv.2 =
        (((runOf p ms).pos (t + 1)).ep == some (toSq sv.1)) := lit_pos _ _ _ _ hrole
    have hzv : sv.2 ≠ 0 := by
      have h0v : 0 < sv.2 := hrole.1
      omega
    have hcolrw1 : (cfgOf w b n m).col (t + 1) = (t + 1) % 2 := rfl
    have hsEp : sv.1 ∈ epSquares (cfgOf w b n m) (t + 1) := by
      have hmap := (roles_eps (cfgOf w b n m) (t + 1) (by omega)).1
      rw [← hmap]
      exact List.mem_map.mpr ⟨sv, hsv, rfl⟩
    have hcore := core_eps hch t ht sv.1 hsEp
    rw [epSquares_eq] at hsEp
    obtain ⟨hsNK, hcond⟩ := List.mem_filter.mp hsEp
    rw [hcolrw1] at hcond
    have hcA := (Bool.and_eq_true _ _).mp hcond
    have hcd2 := (Bool.and_eq_true _ _).mp hcA.1
    have hrkV : rk sv.1 = (if (t + 1) % 2 = 0 then (5 : Int) else 2) := beq_iff_eq.mp hcd2.1
    have hkd : (!(cfgOf w b n m).isK (sqOf (fl sv.1) (rk sv.1 - pdir ((t + 1) % 2)))) = true :=
      hcd2.2
    have hko : (!(cfgOf w b n m).isK (sqOf (fl sv.1) (rk sv.1 + pdir ((t + 1) % 2)))) = true :=
      hcA.2
    have honbmP : onb (fl sv.1) (rk sv.1 - pdir ((t + 1) % 2)) = true := by
      rcases color_parity ((t + 1) % 2) (Nat.mod_lt _ (by decide)) with ⟨he, -, hpd, -, -⟩ |
        ⟨he, -, hpd, -, -⟩
      · rw [hpd]
        have hrk5c : rk sv.1 = 5 := by
          rw [he, ite_eq_left (rfl : (0 : Nat) = 0)] at hrkV
          exact hrkV
        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
        have e : fl sv.1 = ((sv.1 % 8 : Nat) : Int) := rfl
        omega
      · rw [hpd]
        have hrk2c : rk sv.1 = 2 := by
          rw [he, ite_eq_right (by decide)] at hrkV
          exact hrkV
        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
        have e : fl sv.1 = ((sv.1 % 8 : Nat) : Int) := rfl
        omega
    have honbpP : onb (fl sv.1) (rk sv.1 + pdir ((t + 1) % 2)) = true := by
      rcases color_parity ((t + 1) % 2) (Nat.mod_lt _ (by decide)) with ⟨he, -, hpd, -, -⟩ |
        ⟨he, -, hpd, -, -⟩
      · rw [hpd]
        have hrk5c : rk sv.1 = 5 := by
          rw [he, ite_eq_left (rfl : (0 : Nat) = 0)] at hrkV
          exact hrkV
        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
        have e : fl sv.1 = ((sv.1 % 8 : Nat) : Int) := rfl
        omega
      · rw [hpd]
        have hrk2c : rk sv.1 = 2 := by
          rw [he, ite_eq_right (by decide)] at hrkV
          exact hrkV
        simp only [onb, Bool.and_eq_true, decide_eq_true_eq]
        have e : fl sv.1 = ((sv.1 % 8 : Nat) : Int) := rfl
        omega
    obtain ⟨h64m, -, -⟩ := onb_sqOf _ _ honbmP
    obtain ⟨h64p, -, -⟩ := onb_sqOf _ _ honbpP
    have hdsqNK : sqOf (fl sv.1) (rk sv.1 - pdir ((t + 1) % 2)) ∈ (cfgOf w b n m).NK :=
      List.mem_filter.mpr ⟨List.mem_range.mpr h64m, hkd⟩
    have hosqNK : sqOf (fl sv.1) (rk sv.1 + pdir ((t + 1) % 2)) ∈ (cfgOf w b n m).NK :=
      List.mem_filter.mpr ⟨List.mem_range.mpr h64p, hko⟩
    have hefrO : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).FR.getD (sqOf (fl sv.1) (rk sv.1 + pdir ((t + 1) % 2))) 0) =
        (((runOf p ms).mv t).src.val == sqOf (fl sv.1) (rk sv.1 + pdir ((t + 1) % 2))) :=
      lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t _ ht hosqNK).1
    have hzfrO : (((encodeCfg (cfgOf w b n m)).layout.ply t).FR.getD (sqOf (fl sv.1) (rk sv.1 + pdir ((t + 1) % 2))) 0) ≠ 0 := by
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).FR.getD (sqOf (fl sv.1) (rk sv.1 + pdir ((t + 1) % 2))) 0 :=
        (roles_FRTO (cfgOf w b n m) t _ ht hosqNK).1.1
      omega
    have hetoD : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).TO.getD (sqOf (fl sv.1) (rk sv.1 - pdir ((t + 1) % 2))) 0) =
        (((runOf p ms).mv t).dst.val == sqOf (fl sv.1) (rk sv.1 - pdir ((t + 1) % 2))) :=
      lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t _ ht hdsqNK).2
    have hztoD : (((encodeCfg (cfgOf w b n m)).layout.ply t).TO.getD (sqOf (fl sv.1) (rk sv.1 - pdir ((t + 1) % 2))) 0) ≠ 0 := by
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).TO.getD (sqOf (fl sv.1) (rk sv.1 - pdir ((t + 1) % 2))) 0 :=
        (roles_FRTO (cfgOf w b n m) t _ ht hdsqNK).2.1
      omega
    have heMP : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD P 0) =
        (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (fun x => kindIdx x.kind == P) :=
      lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 P (by decide)).1
    have heMP2 : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD P 0) =
        (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn) :=
      heMP.trans (X14.any_kindIdx_pawn _)
    have hzMP : (((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD P 0) ≠ 0 := by
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD P 0 :=
        ((roles_MPRT (cfgOf w b n m) t ht).2.2 P (by decide)).1.1
      omega
    rcases hcl with hcl | hcl | hcl | hcl
    · rw [hcl, hcolrw1]
      cases hevB : (((runOf p ms).pos (t + 1)).ep == some (toSq sv.1))
      · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hevB]; rfl)
      · have hs1 : ((runOf p ms).pos (t + 1)).ep = some (toSq sv.1) := beq_iff_eq.mp hevB
        obtain ⟨hs1a, hs1b, hs1c⟩ := hcore.mp hs1
        exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by rw [hefrO]; exact beq_iff_eq.mpr hs1a)
    · rw [hcl, hcolrw1]
      cases hevB : (((runOf p ms).pos (t + 1)).ep == some (toSq sv.1))
      · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hevB]; rfl)
      · have hs1 : ((runOf p ms).pos (t + 1)).ep = some (toSq sv.1) := beq_iff_eq.mp hevB
        obtain ⟨hs1a, hs1b, hs1c⟩ := hcore.mp hs1
        exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by rw [hetoD]; exact beq_iff_eq.mpr hs1b)
    · rw [hcl]
      cases hevB : (((runOf p ms).pos (t + 1)).ep == some (toSq sv.1))
      · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzv, hev, hevB]; rfl)
      · have hs1 : ((runOf p ms).pos (t + 1)).ep = some (toSq sv.1) := beq_iff_eq.mp hevB
        obtain ⟨hs1a, hs1b, hs1c⟩ := hcore.mp hs1
        exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by rw [heMP2]; exact hs1c)
    · rw [hcl, hcolrw1]
      cases hsc : (((runOf p ms).mv t).src.val == sqOf (fl sv.1) (rk sv.1 + pdir ((t + 1) % 2)))
      · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzfrO, hefrO, hsc]; rfl)
      · cases hdt : (((runOf p ms).mv t).dst.val == sqOf (fl sv.1) (rk sv.1 - pdir ((t + 1) % 2)))
        · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [lit_neg_eval _ _ hztoD, hetoD, hdt]; rfl)
        · cases hap : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (·.kind == .pawn))
          · exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
              (by rw [lit_neg_eval _ _ hzMP, heMP2, hap]; rfl)
          · have hfull : ((runOf p ms).pos (t + 1)).ep = some (toSq sv.1) :=
              hcore.mpr ⟨beq_iff_eq.mp hsc, beq_iff_eq.mp hdt, hap⟩
            exact X13.clause_true
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
              (by rw [hev]; exact beq_iff_eq.mpr hfull)



theorem fam_move1 : FamOK w b n m .move1 := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_flatMap, List.mem_range, List.mem_append] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
  obtain ⟨⟨qc, qk⟩, hqsrc, hqcol, hpiece⟩ := legal_nonking_mem _ _ hleg hkm
  have hturn := run_turn hch t (Nat.le_of_lt ht)
  have hqk : qk ≠ .king := by
    have h1' : (qk == .king) = false := by simpa [isKingMove, hqsrc] using hkm
    intro e
    rw [e] at h1'
    simp at h1'
  have hk5 : kindIdx qk < 5 := X13.kindIdx_lt_of_ne_king qk hqk
  obtain ⟨hsNK, hdNK⟩ := core_src_dst hch t ht
  have hefr : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) = (((runOf p ms).mv t).src.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).1
  have heto : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
  have hzfr : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).fr s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).1.1
    omega
  have hzto : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).2.1
    omega
  have hemp : ∀ k, k < 5 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).mp k) = (kindIdx qk == k) := by
    intro k hk
    refine (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).1).trans ?_
    show (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (fun x => kindIdx x.kind == k) =
      (kindIdx qk == k)
    rw [hqsrc]
    rfl
  have hert : ∀ k, k < 5 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).rt k) =
        (kindIdx (((runOf p ms).mv t).promo.getD qk) == k) := by
    intro k hk
    refine (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).2).trans ?_
    show (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any
        (fun x => kindIdx (((runOf p ms).mv t).promo.getD x.kind) == k) =
      (kindIdx (((runOf p ms).mv t).promo.getD qk) == k)
    rw [hqsrc]
    rfl
  have hMP5 : ((encodeCfg (cfgOf w b n m)).layout.ply t).MP.length = 5 :=
    (roles_MPRT (cfgOf w b n m) t ht).1
  have hRT5 : ((encodeCfg (cfgOf w b n m)).layout.ply t).RT.length = 5 :=
    (roles_MPRT (cfgOf w b n m) t ht).2.1
  have hps : (runOf p ms).mv t ∈ pseudo ((runOf p ms).pos t) := legal_mem_pseudo _ _ hleg
  have hpnek : ((runOf p ms).mv t).promo ≠ some .king := promo_ne_king _ _ hps
  have hpk5 : kindIdx (((runOf p ms).mv t).promo.getD qk) < 5 := by
    cases hpr : ((runOf p ms).mv t).promo with
    | none => exact hk5
    | some k0 => exact X13.kindIdx_lt_of_ne_king k0 (fun e => hpnek (by rw [hpr, e]))
  have hfafr : Fa2 (fun l v => Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) l = v)
      ((cfgOf w b n m).NK.map ((encodeCfg (cfgOf w b n m)).layout.ply t).fr)
      ((cfgOf w b n m).NK.map fun s => ((runOf p ms).mv t).src.val == s) :=
    X13.fa2_map_of _ _ _ _ fun s hs => hefr s hs
  have hfato : Fa2 (fun l v => Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) l = v)
      ((cfgOf w b n m).NK.map ((encodeCfg (cfgOf w b n m)).layout.ply t).to)
      ((cfgOf w b n m).NK.map fun s => ((runOf p ms).mv t).dst.val == s) :=
    X13.fa2_map_of _ _ _ _ fun s hs => heto s hs
  have hcntfr :
      (((cfgOf w b n m).NK.map fun s => ((runOf p ms).mv t).src.val == s).filter id).length ≤ 1 :=
    X13.cnt_beq_nodup _ _ (X13.nk_nodup _)
  have hcntto :
      (((cfgOf w b n m).NK.map fun s => ((runOf p ms).mv t).dst.val == s).filter id).length ≤ 1 :=
    X13.cnt_beq_nodup _ _ (X13.nk_nodup _)
  have hzf : ∀ l ∈ (cfgOf w b n m).NK.map ((encodeCfg (cfgOf w b n m)).layout.ply t).fr, l ≠ 0 := by
    intro l hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    exact hzfr s hs
  have hzt : ∀ l ∈ (cfgOf w b n m).NK.map ((encodeCfg (cfgOf w b n m)).layout.ply t).to, l ≠ 0 := by
    intro l hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    exact hzto s hs
  have hzlFRL : ∀ l ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).FRL, l ≠ 0 := by
    intro l hl
    obtain ⟨i, hi, hget⟩ := X13.mem_getD' 0 hl
    have hi' : i < (cfgOf w b n m).NK.length - 1 := by
      have e : ((encodeCfg (cfgOf w b n m)).layout.ply t).FRL.length = (cfgOf w b n m).NK.length - 1 :=
        (roles_FRTOL (cfgOf w b n m) t ht).1
      omega
    rw [← hget]
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).FRL.getD i 0 :=
      ((roles_FRTOL (cfgOf w b n m) t ht).2.2 i hi').1.1
    omega
  have hzlTOL : ∀ l ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).TOL, l ≠ 0 := by
    intro l hl
    obtain ⟨i, hi, hget⟩ := X13.mem_getD' 0 hl
    have hi' : i < (cfgOf w b n m).NK.length - 1 := by
      have e : ((encodeCfg (cfgOf w b n m)).layout.ply t).TOL.length = (cfgOf w b n m).NK.length - 1 :=
        (roles_FRTOL (cfgOf w b n m) t ht).2.1
      omega
    rw [← hget]
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).TOL.getD i 0 :=
      ((roles_FRTOL (cfgOf w b n m) t ht).2.2 i hi').2.1
    omega
  have hladfr : 8 < ((cfgOf w b n m).NK.map ((encodeCfg (cfgOf w b n m)).layout.ply t).fr).length →
      ((encodeCfg (cfgOf w b n m)).layout.ply t).FRL.length =
        ((cfgOf w b n m).NK.map ((encodeCfg (cfgOf w b n m)).layout.ply t).fr).length - 1 ∧
        ∀ i, i < ((encodeCfg (cfgOf w b n m)).layout.ply t).FRL.length →
          Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
            (((encodeCfg (cfgOf w b n m)).layout.ply t).FRL.getD i 0) =
            (((cfgOf w b n m).NK.map fun s =>
              ((runOf p ms).mv t).src.val == s).take (i + 1)).any id := by
    intro h8
    constructor
    · rw [List.length_map]
      exact (roles_FRTOL (cfgOf w b n m) t ht).1
    · intro i hi
      have hi' : i < (cfgOf w b n m).NK.length - 1 := by
        have e : ((encodeCfg (cfgOf w b n m)).layout.ply t).FRL.length =
            (cfgOf w b n m).NK.length - 1 := (roles_FRTOL (cfgOf w b n m) t ht).1
        omega
      refine (lit_pos _ _ _ _ ((roles_FRTOL (cfgOf w b n m) t ht).2.2 i hi').1).trans ?_
      show (((cfgOf w b n m).NK.map (Sem.fr t)).take (i + 1)).any
          (fun a => a.val (encodeCfg (cfgOf w b n m)).cfg (runOf p ms)) =
        (((cfgOf w b n m).NK.map fun s => ((runOf p ms).mv t).src.val == s).take (i + 1)).any id
      exact X13.take_any_map_sem _ _ _ _ _ _ fun s hs => rfl
  have hladto : 8 < ((cfgOf w b n m).NK.map ((encodeCfg (cfgOf w b n m)).layout.ply t).to).length →
      ((encodeCfg (cfgOf w b n m)).layout.ply t).TOL.length =
        ((cfgOf w b n m).NK.map ((encodeCfg (cfgOf w b n m)).layout.ply t).to).length - 1 ∧
        ∀ i, i < ((encodeCfg (cfgOf w b n m)).layout.ply t).TOL.length →
          Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
            (((encodeCfg (cfgOf w b n m)).layout.ply t).TOL.getD i 0) =
            (((cfgOf w b n m).NK.map fun s =>
              ((runOf p ms).mv t).dst.val == s).take (i + 1)).any id := by
    intro h8
    constructor
    · rw [List.length_map]
      exact (roles_FRTOL (cfgOf w b n m) t ht).2.1
    · intro i hi
      have hi' : i < (cfgOf w b n m).NK.length - 1 := by
        have e : ((encodeCfg (cfgOf w b n m)).layout.ply t).TOL.length =
            (cfgOf w b n m).NK.length - 1 := (roles_FRTOL (cfgOf w b n m) t ht).2.1
        omega
      refine (lit_pos _ _ _ _ ((roles_FRTOL (cfgOf w b n m) t ht).2.2 i hi').2).trans ?_
      show (((cfgOf w b n m).NK.map (Sem.to t)).take (i + 1)).any
          (fun a => a.val (encodeCfg (cfgOf w b n m)).cfg (runOf p ms)) =
        (((cfgOf w b n m).NK.map fun s => ((runOf p ms).mv t).dst.val == s).take (i + 1)).any id
      exact X13.take_any_map_sem _ _ _ _ _ _ fun s hs => rfl
  have hMPe : ((encodeCfg (cfgOf w b n m)).layout.ply t).MP =
      (List.range 5).map fun i => ((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD i 0 := by
    have e := X13.list_eq_range_getD (0 : Int) (((encodeCfg (cfgOf w b n m)).layout.ply t).MP)
    rw [hMP5] at e
    exact e
  have hRTe : ((encodeCfg (cfgOf w b n m)).layout.ply t).RT =
      (List.range 5).map fun i => ((encodeCfg (cfgOf w b n m)).layout.ply t).RT.getD i 0 := by
    have e := X13.list_eq_range_getD (0 : Int) (((encodeCfg (cfgOf w b n m)).layout.ply t).RT)
    rw [hRT5] at e
    exact e
  have hfaMP : Fa2 (fun l v => Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) l = v)
      ((encodeCfg (cfgOf w b n m)).layout.ply t).MP ((List.range 5).map fun k => (kindIdx qk == k)) := by
    rw [hMPe]
    exact X13.fa2_map_of _ _ _ _ fun k hk => hemp k (List.mem_range.mp hk)
  have hfaRT : Fa2 (fun l v => Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) l = v)
      ((encodeCfg (cfgOf w b n m)).layout.ply t).RT
      ((List.range 5).map fun k => (kindIdx (((runOf p ms).mv t).promo.getD qk) == k)) := by
    rw [hRTe]
    exact X13.fa2_map_of _ _ _ _ fun k hk => hert k (List.mem_range.mp hk)
  have hzMP : ∀ l ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).MP, l ≠ 0 := by
    intro l hl
    obtain ⟨i, hi, hget⟩ := X13.mem_getD' 0 hl
    have hi' : i < 5 := by rw [hMP5] at hi; exact hi
    rw [← hget]
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD i 0 :=
      ((roles_MPRT (cfgOf w b n m) t ht).2.2 i hi').1.1
    omega
  have hzRT : ∀ l ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).RT, l ≠ 0 := by
    intro l hl
    obtain ⟨i, hi, hget⟩ := X13.mem_getD' 0 hl
    have hi' : i < 5 := by
      have e := hRT5
      omega
    rw [← hget]
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).RT.getD i 0 :=
      ((roles_MPRT (cfgOf w b n m) t ht).2.2 i hi').2.1
    omega
  have hcntMP : (((List.range 5).map fun k => (kindIdx qk == k)).filter id).length ≤ 1 :=
    X13.cnt_beq_nodup _ _ List.nodup_range
  have hcntRT :
      (((List.range 5).map fun k =>
        (kindIdx (((runOf p ms).mv t).promo.getD qk) == k)).filter id).length ≤ 1 :=
    X13.cnt_beq_nodup _ _ List.nodup_range
  rcases hfm with hmv | hsq
  · obtain hdisj := X13.mem_plyMove1Cls (cfgOf w b n m) c _ hmv
    rcases hdisj with hm | hfr | hm | hto | hm | hmp | hm | hrt
    · rw [hm]
      exact X13.clause_true (List.mem_map.mpr ⟨_, hsNK, rfl⟩) (by rw [hefr _ hsNK]; exact beq_self_eq_true _)
    · exact amo_sound _ ((cfgOf w b n m).NK.map ((encodeCfg (cfgOf w b n m)).layout.ply t).fr)
        (((encodeCfg (cfgOf w b n m)).layout.ply t).FRL)
        ((cfgOf w b n m).NK.map fun s => ((runOf p ms).mv t).src.val == s) hzf hzlFRL hfafr hcntfr
        hladfr c.1 hfr
    · rw [hm]
      exact X13.clause_true (List.mem_map.mpr ⟨_, hdNK, rfl⟩) (by rw [heto _ hdNK]; exact beq_self_eq_true _)
    · exact amo_sound _ ((cfgOf w b n m).NK.map ((encodeCfg (cfgOf w b n m)).layout.ply t).to)
        (((encodeCfg (cfgOf w b n m)).layout.ply t).TOL)
        ((cfgOf w b n m).NK.map fun s => ((runOf p ms).mv t).dst.val == s) hzt hzlTOL hfato hcntto
        hladto c.1 hto
    · rw [hm]
      exact X13.clause_true
        (show ((encodeCfg (cfgOf w b n m)).layout.ply t).mp (kindIdx qk) ∈
          ((encodeCfg (cfgOf w b n m)).layout.ply t).MP from
          getD_mem _ _ _ (by rw [hMP5]; exact hk5))
        (by rw [hemp (kindIdx qk) hk5]; exact beq_self_eq_true _)
    · exact amo_sound _ (((encodeCfg (cfgOf w b n m)).layout.ply t).MP) []
        ((List.range 5).map fun k => (kindIdx qk == k)) hzMP (fun l hl => absurd hl (by simp)) hfaMP
        hcntMP (fun h8 => absurd (by rw [hMP5] at h8; exact h8) (by decide)) c.1 hmp
    · rw [hm]
      exact X13.clause_true
        (show ((encodeCfg (cfgOf w b n m)).layout.ply t).rt (kindIdx (((runOf p ms).mv t).promo.getD qk)) ∈
          ((encodeCfg (cfgOf w b n m)).layout.ply t).RT from
          getD_mem _ _ _ (by rw [hRT5]; exact hpk5))
        (by rw [hert (kindIdx (((runOf p ms).mv t).promo.getD qk)) hpk5]; exact beq_self_eq_true _)
    · exact amo_sound _ (((encodeCfg (cfgOf w b n m)).layout.ply t).RT) []
        ((List.range 5).map fun k => (kindIdx (((runOf p ms).mv t).promo.getD qk) == k)) hzRT
        (fun l hl => absurd hl (by simp)) hfaRT hcntRT
        (fun h8 => absurd (by rw [hRT5] at h8; exact h8) (by decide)) c.1 hrt
  · obtain ⟨s, hs, hsq⟩ := mem_plySqCls (cfgOf w b n m) c t _ _ hsq
    rcases hsq with h1' | h2' | h3'
    · obtain ⟨-, hm1⟩ := mem_tag _ _ _ h1'
      rw [List.mem_singleton.mp hm1]
      cases hfrv : (((runOf p ms).mv t).src.val == s)
      · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ (hzfr s hs), hefr s hs, hfrv]; rfl)
      · cases htov : (((runOf p ms).mv t).dst.val == s)
        · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [lit_neg_eval _ _ (hzto s hs), heto s hs, htov]; rfl)
        · exfalso
          have e1 := beq_iff_eq.mp hfrv
          have e2 := beq_iff_eq.mp htov
          exact legal_src_ne_dst _ _ hleg (Fin.ext (e1.trans e2.symm))
    · obtain ⟨hf2, -⟩ := mem_tag _ _ _ h2'
      rw [hf2] at hf
      exact absurd hf (by decide)
    · obtain ⟨hf2, -⟩ := mem_tag _ _ _ h3'
      rw [hf2] at hf
      exact absurd hf (by decide)

theorem fam_source : FamOK w b n m .source := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_flatMap, List.mem_range] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
  obtain ⟨⟨qc, qk⟩, hqsrc, hqcol, hpiece⟩ := legal_nonking_mem _ _ hleg hkm
  have hturn := run_turn hch t (Nat.le_of_lt ht)
  have hqk : qk ≠ .king := by
    have h1' : (qk == .king) = false := by simpa [isKingMove, hqsrc] using hkm
    intro e
    rw [e] at h1'
    simp at h1'
  have hk5 : kindIdx qk < 5 := X13.kindIdx_lt_of_ne_king qk hqk
  have hqcol2 : qc = ((runOf p ms).pos t).turn := hqcol
  have hqcc : qc = colorOf (t % 2) := hqcol2.trans hturn
  have hqci : colIdx qc = t % 2 := by rw [hqcc]; exact X13.colIdx_colorOf _ (Nat.mod_lt _ (by decide))
  have hct : (cfgOf w b n m).col t = t % 2 := rfl
  have hbnd : 5 * (cfgOf w b n m).col t + kindIdx qk < 11 := by
    rw [hct]
    have h1c : t % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have hbndp : ∀ p0, p0 < 5 → 5 * (cfgOf w b n m).col t + p0 < 11 := by
    intro p0 hp0
    rw [hct]
    have h1c : t % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have hefr : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) = (((runOf p ms).mv t).src.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).1
  have hzfr : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).fr s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).1.1
    omega
  have hemp : ∀ k, k < 5 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).mp k) = (kindIdx qk == k) := by
    intro k hk
    refine (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).1).trans ?_
    show (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (fun x => kindIdx x.kind == k) =
      (kindIdx qk == k)
    rw [hqsrc]
    rfl
  have hzmp : ∀ k, k < 5 → (((encodeCfg (cfgOf w b n m)).layout.ply t).mp k) ≠ 0 := by
    intro k hk
    show ((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD k 0 ≠ 0
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD k 0 :=
      ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).1.1
    omega
  have hex : ∀ s ∈ (cfgOf w b n m).NK, ∀ k, k < 11 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k) =
        (code (((runOf p ms).pos t).board (toSq s)) == k) :=
    fun s hs k hk => lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t s k (Nat.le_of_lt ht) hs hk)
  have hzx : ∀ s ∈ (cfgOf w b n m).NK, ∀ k, k < 11 →
      xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k ≠ 0 := by
    intro s hs k hk
    show xv (((encodeCfg (cfgOf w b n m)).layout.X.getD t #[])) s k ≠ 0
    have h0 : 0 < xv (((encodeCfg (cfgOf w b n m)).layout.X.getD t #[])) s k :=
      (roles_X (cfgOf w b n m) t s k (Nat.le_of_lt ht) hs hk).1
    omega
  obtain ⟨s, hs, hsq⟩ := mem_plySqCls (cfgOf w b n m) c t _ _ hfm
  rcases hsq with h1' | h2' | h3'
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ h1'
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨-, hm⟩ := mem_tag _ _ _ h2'
    simp only [List.mem_cons, List.mem_flatMap, List.mem_range] at hm
    rcases hm with hm | ⟨p0, hp0, hm⟩
    · rw [hm]
      cases hfrv : (((runOf p ms).mv t).src.val == s)
      · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ (hzfr s hs), hefr s hs, hfrv]; rfl)
      · have e1 : ((runOf p ms).mv t).src.val = s := beq_iff_eq.mp hfrv
        exact X13.clause_true
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨kindIdx qk, List.mem_range.mpr hk5, rfl⟩))
          (by
            rw [hex s hs _ hbnd, ← e1, toSq_val, hqsrc, X13.code_nonking qc qk hqk, hqci]
            exact beq_self_eq_true _)
    · rcases hm with hm | hm | hm
      · rw [hm]
        cases hfrv : (((runOf p ms).mv t).src.val == s)
        · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ (hzfr s hs), hefr s hs, hfrv]; rfl)
        · cases hmpv : (kindIdx qk == p0)
          · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
              (by
                rw [lit_neg_eval _ _ (hzmp p0 hp0), hemp p0 hp0, hmpv]
                rfl)
          · have e1 : ((runOf p ms).mv t).src.val = s := beq_iff_eq.mp hfrv
            have e2 : kindIdx qk = p0 := beq_iff_eq.mp hmpv
            exact X13.clause_true
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
              (by
                rw [hex s hs _ (hbndp p0 hp0), ← e1, toSq_val, hqsrc,
                  X13.code_nonking qc qk hqk, hqci, ← e2]
                exact beq_self_eq_true _)
      · rw [hm]
        cases hfrv : (((runOf p ms).mv t).src.val == s)
        · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ (hzfr s hs), hefr s hs, hfrv]; rfl)
        · have e1 : ((runOf p ms).mv t).src.val = s := beq_iff_eq.mp hfrv
          have hbd : code (((runOf p ms).pos t).board (toSq s)) = 5 * (t % 2) + kindIdx qk := by
            rw [← e1, toSq_val, hqsrc, X13.code_nonking qc qk hqk, hqci]
          cases hxvv : (code (((runOf p ms).pos t).board (toSq s)) == 5 * (cfgOf w b n m).col t + p0)
          · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
              (by
                rw [lit_neg_eval _ _ (hzx s hs _ (hbndp p0 hp0)),
                  hex s hs _ (hbndp p0 hp0), hxvv]
                rfl)
          · have hx2 : code (((runOf p ms).pos t).board (toSq s)) =
                5 * (cfgOf w b n m).col t + p0 := beq_iff_eq.mp hxvv
            rw [hct] at hx2
            rw [hbd] at hx2
            have hkq : kindIdx qk = p0 := by omega
            exact X13.clause_true
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
              (by rw [hemp p0 hp0, hkq]; exact beq_self_eq_true _)
      · exact absurd hm (by simp)
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ h3'
    rw [hf2] at hf
    exact absurd hf (by decide)

theorem fam_dest : FamOK w b n m .dest := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_flatMap, List.mem_range] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
  have hturn := run_turn hch t (Nat.le_of_lt ht)
  have hct : (cfgOf w b n m).col t = t % 2 := rfl
  have hbndp : ∀ p0, p0 < 5 → 5 * (cfgOf w b n m).col t + p0 < 11 := by
    intro p0 hp0
    rw [hct]
    have h1c : t % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have heto : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
  have hzto : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).2.1
    omega
  have hex : ∀ s ∈ (cfgOf w b n m).NK, ∀ k, k < 11 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k) =
        (code (((runOf p ms).pos t).board (toSq s)) == k) :=
    fun s hs k hk => lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t s k (Nat.le_of_lt ht) hs hk)
  have hzx : ∀ s ∈ (cfgOf w b n m).NK, ∀ k, k < 11 →
      xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k ≠ 0 := by
    intro s hs k hk
    show xv (((encodeCfg (cfgOf w b n m)).layout.X.getD t #[])) s k ≠ 0
    have h0 : 0 < xv (((encodeCfg (cfgOf w b n m)).layout.X.getD t #[])) s k :=
      (roles_X (cfgOf w b n m) t s k (Nat.le_of_lt ht) hs hk).1
    omega
  obtain ⟨s, hs, hsq⟩ := mem_plySqCls (cfgOf w b n m) c t _ _ hfm
  rcases hsq with h1' | h2' | h3'
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ h1'
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ h2'
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨-, hm⟩ := mem_tag _ _ _ h3'
    obtain ⟨p0, hp0, hcc⟩ := List.mem_map.mp hm
    rw [← hcc]
    cases htd : (((runOf p ms).mv t).dst.val == s)
    · show Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        [-((encodeCfg (cfgOf w b n m)).layout.ply t).to s,
          -xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s (5 * (cfgOf w b n m).col t + p0)] = true
      exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ (hzto s hs), heto s hs, htd]; rfl)
    · cases hxvv : (code (((runOf p ms).pos t).board (toSq s)) == 5 * (cfgOf w b n m).col t + p0)
      · show Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
          [-((encodeCfg (cfgOf w b n m)).layout.ply t).to s,
            -xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s (5 * (cfgOf w b n m).col t + p0)] = true
        exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by
            rw [lit_neg_eval _ _ (hzx s hs _ (hbndp p0 (List.mem_range.mp hp0))),
              hex s hs _ (hbndp p0 (List.mem_range.mp hp0)), hxvv]
            rfl)
      · exfalso
        have e2 : ((runOf p ms).mv t).dst.val = s := beq_iff_eq.mp htd
        have hx2 : code (((runOf p ms).pos t).board (toSq s)) =
            5 * (cfgOf w b n m).col t + p0 := beq_iff_eq.mp hxvv
        rw [hct] at hx2
        obtain ⟨c'', k'', hbd, hci, hki⟩ :=
          X13.code_of_eq _ (t % 2) p0 (Nat.mod_lt _ (by decide)) (List.mem_range.mp hp0) hx2
        rw [← e2, toSq_val] at hbd
        have hclr : c'' = ((runOf p ms).pos t).turn :=
          (X13.eq_colorOf_colIdx c'' _ (Nat.mod_lt _ (by decide)) hci).trans hturn.symm
        exact legal_dst_not_own _ _ hleg ⟨c'', k''⟩ hbd hclr

theorem fam_geom : FamOK w b n m .geom := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_flatMap, List.mem_range] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
  obtain ⟨⟨qc, qk⟩, hqsrc, hqcol, hpiece⟩ := legal_nonking_mem _ _ hleg hkm
  have hturn := run_turn hch t (Nat.le_of_lt ht)
  have hqk : qk ≠ .king := by
    have h1' : (qk == .king) = false := by simpa [isKingMove, hqsrc] using hkm
    intro e
    rw [e] at h1'
    simp at h1'
  have hk5 : kindIdx qk < 5 := X13.kindIdx_lt_of_ne_king qk hqk
  have hefr : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) = (((runOf p ms).mv t).src.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).1
  have heto : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
  have hzfr : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).fr s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).1.1
    omega
  have hzto : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).2.1
    omega
  have hemp : ∀ k, k < 5 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).mp k) = (kindIdx qk == k) := by
    intro k hk
    refine (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).1).trans ?_
    show (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (fun x => kindIdx x.kind == k) =
      (kindIdx qk == k)
    rw [hqsrc]
    rfl
  obtain ⟨f, hfi, h, hhi, hfh, hpc⟩ := mem_plyGeomCls (cfgOf w b n m) c t _ _ hfm
  obtain hpc := X13.mem_plyPairCls (cfgOf w b n m) t _ _ f h c hpc
  rcases hpc with ⟨he, hpc⟩ | ⟨hef, hl5, hpc⟩ | hpc | ⟨hcon, hfl, hpc⟩ | ⟨hcon, hfl, hpc⟩
  · obtain ⟨-, hm⟩ := mem_tag _ _ _ hpc
    rw [List.mem_singleton.mp hm]
    cases hfrv : (((runOf p ms).mv t).src.val == f)
    · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ (hzfr f hfi), hefr f hfi, hfrv]; rfl)
    · cases htov : (((runOf p ms).mv t).dst.val == h)
      · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by rw [lit_neg_eval _ _ (hzto h hhi), heto h hhi, htov]; rfl)
      · obtain ⟨q'', hq'', hconk⟩ := core_allowed hch t ht
        have hq2 : q'' = ⟨qc, qk⟩ := Option.some.inj (hq''.symm.trans hqsrc)
        rw [hq2] at hconk
        have e1 : ((runOf p ms).mv t).src.val = f := beq_iff_eq.mp hfrv
        have e2 : ((runOf p ms).mv t).dst.val = h := beq_iff_eq.mp htov
        rw [e1, e2] at hconk
        have hcon2 : ((cfgOf w b n m).allowed ((cfgOf w b n m).col t) f h).contains (kindIdx qk) = true :=
          hconk
        rw [X13.isEmpty_nil he] at hcon2
        rw [show ([] : List Nat).contains (kindIdx qk) = false from rfl] at hcon2
        exact absurd hcon2 (by decide)
  · obtain ⟨-, hm⟩ := mem_tag _ _ _ hpc
    rw [List.mem_singleton.mp hm]
    cases hfrv : (((runOf p ms).mv t).src.val == f)
    · exact X13.clause_true (List.mem_append.mpr (Or.inl List.mem_cons_self))
        (by rw [lit_neg_eval _ _ (hzfr f hfi), hefr f hfi, hfrv]; rfl)
    · cases htov : (((runOf p ms).mv t).dst.val == h)
      · exact X13.clause_true (List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)))
          (by rw [lit_neg_eval _ _ (hzto h hhi), heto h hhi, htov]; rfl)
      · obtain ⟨q'', hq'', hconk⟩ := core_allowed hch t ht
        have hq2 : q'' = ⟨qc, qk⟩ := Option.some.inj (hq''.symm.trans hqsrc)
        rw [hq2] at hconk
        have e1 : ((runOf p ms).mv t).src.val = f := beq_iff_eq.mp hfrv
        have e2 : ((runOf p ms).mv t).dst.val = h := beq_iff_eq.mp htov
        rw [e1, e2] at hconk
        have hmem : kindIdx qk ∈ (cfgOf w b n m).allowed ((cfgOf w b n m).col t) f h :=
          List.contains_iff_mem.mp hconk
        exact X13.clause_true
          (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨kindIdx qk, hmem, rfl⟩)))
          (by rw [hemp (kindIdx qk) hk5]; exact beq_self_eq_true _)
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ hpc
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ hpc
    rw [hf2] at hf
    exact absurd hf (by decide)
  · rcases hpc with ⟨v, hv, hpc⟩ | ⟨hv, hpc⟩ <;> obtain ⟨hf2, -⟩ := mem_tag _ _ _ hpc <;>
      rw [hf2] at hf <;> exact absurd hf (by decide)

theorem fam_transit : FamOK w b n m .transit := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_flatMap, List.mem_range] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
  have hefr : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) = (((runOf p ms).mv t).src.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).1
  have heto : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
  have hzfr : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).fr s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).1.1
    omega
  have hzto : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).2.1
    omega
  have hex : ∀ s ∈ (cfgOf w b n m).NK, ∀ k, k < 11 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k) =
        (code (((runOf p ms).pos t).board (toSq s)) == k) :=
    fun s hs k hk => lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t s k (Nat.le_of_lt ht) hs hk)
  obtain ⟨f, hfi, h, hhi, hfh, hpc⟩ := mem_plyGeomCls (cfgOf w b n m) c t _ _ hfm
  obtain hpc := X13.mem_plyPairCls (cfgOf w b n m) t _ _ f h c hpc
  rcases hpc with ⟨he, hpc⟩ | ⟨hef, hl5, hpc⟩ | hpc | ⟨hcon, hfl, hpc⟩ | ⟨hcon, hfl, hpc⟩
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ hpc
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ hpc
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨-, hm⟩ := mem_tag _ _ _ hpc
    obtain ⟨z, hzb, hcc⟩ := List.mem_map.mp hm
    rw [← hcc]
    show Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
      [-((encodeCfg (cfgOf w b n m)).layout.ply t).fr f, -((encodeCfg (cfgOf w b n m)).layout.ply t).to h,
        xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) z EMP] = true
    cases hfrv : (((runOf p ms).mv t).src.val == f)
    · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ (hzfr f hfi), hefr f hfi, hfrv]; rfl)
    · cases htov : (((runOf p ms).mv t).dst.val == h)
      · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by rw [lit_neg_eval _ _ (hzto h hhi), heto h hhi, htov]; rfl)
      · have e1 : ((runOf p ms).mv t).src.val = f := beq_iff_eq.mp hfrv
        have e2 : ((runOf p ms).mv t).dst.val = h := beq_iff_eq.mp htov
        have hzb' : z ∈ btw ((runOf p ms).mv t).src.val ((runOf p ms).mv t).dst.val := by
          rw [e1, e2]
          exact hzb
        have hbn : ((runOf p ms).pos t).board (toSq z) = none := core_transit hch t ht z hzb'
        have hzlt : z < 64 := btw_lt ((runOf p ms).mv t).src ((runOf p ms).mv t).dst z hzb'
        have hkw : ((runOf p ms).pos t).board w = some ⟨.white, .king⟩ :=
          (run_kings hch t (Nat.le_of_lt ht)).1
        have hkb : ((runOf p ms).pos t).board b = some ⟨.black, .king⟩ :=
          (run_kings hch t (Nat.le_of_lt ht)).2.1
        have hzw : (z == w.val) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          rw [e, toSq_val] at hbn
          rw [hkw] at hbn
          exact absurd hbn (by decide)
        have hzb'' : (z == b.val) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          rw [e, toSq_val] at hbn
          rw [hkb] at hbn
          exact absurd hbn (by decide)
        have hzNK : z ∈ (cfgOf w b n m).NK :=
          List.mem_filter.mpr ⟨List.mem_range.mpr hzlt, by
            show (!((z == w.val) || (z == b.val))) = true
            rw [hzw, hzb'']
            rfl⟩
        exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (by rw [hex z hzNK EMP (by decide), hbn]; rfl)
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ hpc
    rw [hf2] at hf
    exact absurd hf (by decide)
  · rcases hpc with ⟨v, hv, hpc⟩ | ⟨hv, hpc⟩ <;> obtain ⟨hf2, -⟩ := mem_tag _ _ _ hpc <;>
      rw [hf2] at hf <;> exact absurd hf (by decide)

theorem fam_pawn : FamOK w b n m .pawn := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_flatMap, List.mem_range] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
  obtain ⟨⟨qc, qk⟩, hqsrc, hqcol, hpiece⟩ := legal_nonking_mem _ _ hleg hkm
  have hturn := run_turn hch t (Nat.le_of_lt ht)
  have hqk : qk ≠ .king := by
    have h1' : (qk == .king) = false := by simpa [isKingMove, hqsrc] using hkm
    intro e
    rw [e] at h1'
    simp at h1'
  have hk5 : kindIdx qk < 5 := X13.kindIdx_lt_of_ne_king qk hqk
  have hqcol2 : qc = ((runOf p ms).pos t).turn := hqcol
  have hqcc : qc = colorOf (t % 2) := hqcol2.trans hturn
  have hct : (cfgOf w b n m).col t = t % 2 := rfl
  have hefr : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) = (((runOf p ms).mv t).src.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).1
  have heto : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
  have hzfr : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).fr s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).1.1
    omega
  have hzto : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).2.1
    omega
  have hemp : ∀ k, k < 5 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).mp k) = (kindIdx qk == k) := by
    intro k hk
    refine (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).1).trans ?_
    show (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (fun x => kindIdx x.kind == k) =
      (kindIdx qk == k)
    rw [hqsrc]
    rfl
  have hzmp : ∀ k, k < 5 → (((encodeCfg (cfgOf w b n m)).layout.ply t).mp k) ≠ 0 := by
    intro k hk
    show ((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD k 0 ≠ 0
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD k 0 :=
      ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).1.1
    omega
  have hex : ∀ s ∈ (cfgOf w b n m).NK, ∀ k, k < 11 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k) =
        (code (((runOf p ms).pos t).board (toSq s)) == k) :=
    fun s hs k hk => lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t s k (Nat.le_of_lt ht) hs hk)
  have hzx : ∀ s ∈ (cfgOf w b n m).NK, ∀ k, k < 11 →
      xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k ≠ 0 := by
    intro s hs k hk
    show xv (((encodeCfg (cfgOf w b n m)).layout.X.getD t #[])) s k ≠ 0
    have h0 : 0 < xv (((encodeCfg (cfgOf w b n m)).layout.X.getD t #[])) s k :=
      (roles_X (cfgOf w b n m) t s k (Nat.le_of_lt ht) hs hk).1
    omega
  obtain ⟨f, hfi, h, hhi, hfh, hpc⟩ := mem_plyGeomCls (cfgOf w b n m) c t _ _ hfm
  obtain hpc := X13.mem_plyPairCls (cfgOf w b n m) t _ _ f h c hpc
  rcases hpc with ⟨he, hpc⟩ | ⟨hef, hl5, hpc⟩ | hpc | ⟨hcon, hfl, hpc⟩ | ⟨hcon, hfl, hpc⟩
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ hpc
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ hpc
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨hf2, -⟩ := mem_tag _ _ _ hpc
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨-, hm⟩ := mem_tag _ _ _ hpc
    rw [List.mem_singleton.mp hm]
    cases hfrv : (((runOf p ms).mv t).src.val == f)
    · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ (hzfr f hfi), hefr f hfi, hfrv]; rfl)
    · cases htov : (((runOf p ms).mv t).dst.val == h)
      · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by rw [lit_neg_eval _ _ (hzto h hhi), heto h hhi, htov]; rfl)
      · cases hmpv : (kindIdx qk == P)
        · exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            (by rw [lit_neg_eval _ _ (hzmp P (by decide)), hemp P (by decide), hmpv]; rfl)
        · have hqp : qk = .pawn := X13.kindIdx_eq_P qk (beq_iff_eq.mp hmpv)
          have hpsrc : ((runOf p ms).pos t).board ((runOf p ms).mv t).src = some ⟨colorOf (t % 2), .pawn⟩ := by
            rw [hqsrc, hqcc, hqp]
          have e1 : ((runOf p ms).mv t).src.val = f := beq_iff_eq.mp hfrv
          have e2 : ((runOf p ms).mv t).dst.val = h := beq_iff_eq.mp htov
          have hfx : fx ((runOf p ms).mv t).src = fx ((runOf p ms).mv t).dst := by
            rw [fx_sq, fx_sq, e1, e2]
            exact hfl
          obtain ⟨hcp1, hcp2⟩ := core_pawn hch t ht hpsrc
          have hbn : ((runOf p ms).pos t).board ((runOf p ms).mv t).dst = none := hcp1 hfx
          exact X13.clause_true
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self)))
            (by
              rw [hex h hhi EMP (by decide)]
              rw [← e2, toSq_val, hbn]
              rfl)
  · rcases hpc with ⟨v, hvlook, hpc⟩ | ⟨hvlook, hpc⟩
    · obtain ⟨-, hm⟩ := mem_tag _ _ _ hpc
      rw [List.mem_singleton.mp hm]
      cases hfrv : (((runOf p ms).mv t).src.val == f)
      · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ (hzfr f hfi), hefr f hfi, hfrv]; rfl)
      · cases htov : (((runOf p ms).mv t).dst.val == h)
        · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [lit_neg_eval _ _ (hzto h hhi), heto h hhi, htov]; rfl)
        · cases hmpv : (kindIdx qk == P)
          · exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
              (by rw [lit_neg_eval _ _ (hzmp P (by decide)), hemp P (by decide), hmpv]; rfl)
          · have hqp : qk = .pawn := X13.kindIdx_eq_P qk (beq_iff_eq.mp hmpv)
            have hpsrc : ((runOf p ms).pos t).board ((runOf p ms).mv t).src =
                some ⟨colorOf (t % 2), .pawn⟩ := by
              rw [hqsrc, hqcc, hqp]
            have e1 : ((runOf p ms).mv t).src.val = f := beq_iff_eq.mp hfrv
            have e2 : ((runOf p ms).mv t).dst.val = h := beq_iff_eq.mp htov
            have hfxne : fx ((runOf p ms).mv t).src ≠ fx ((runOf p ms).mv t).dst := by
              rw [fx_sq, fx_sq, e1, e2]
              exact hfl
            obtain ⟨hcp1, hcp2⟩ := core_pawn hch t ht hpsrc
            cases hxvv : (code (((runOf p ms).pos t).board (toSq h)) == EMP)
            · exact X13.clause_true
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ List.mem_cons_self)))
                (by
                  rw [lit_neg_eval _ _ (hzx h hhi EMP (by decide)), hex h hhi EMP (by decide), hxvv]
                  rfl)
            · obtain hbb | ⟨v0, hv0, hv0val⟩ := hcp2 hfxne
              · have hcod : (code (((runOf p ms).pos t).board (toSq h)) == EMP) = false := by
                  rw [← e2, toSq_val]
                  cases hbt : ((runOf p ms).pos t).board ((runOf p ms).mv t).dst with
                  | none => exact absurd hbt hbb
                  | some qq => exact X13.code_ne_emp_of_some qq
                rw [hcod] at hxvv
                exact absurd hxvv (by decide)
              · rw [e2] at hv0val
                have hv0val' : v0.val = sqOf (fl h) (rk h - pdir ((cfgOf w b n m).col t)) := hv0val
                have hrole := (roles_EPR (cfgOf w b n m) t ht).2 _ (X13.mem_of_look hvlook)
                exact X13.clause_true
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
                  (by
                    refine (lit_pos _ _ _ _ hrole).trans ?_
                    show (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) ==
                        some (toSq (sqOf (fl h) (rk h - pdir ((cfgOf w b n m).col t))))) = true
                    rw [hv0, ← hv0val', toSq_val]
                    exact beq_self_eq_true _)
    · obtain ⟨-, hm⟩ := mem_tag _ _ _ hpc
      rw [List.mem_singleton.mp hm]
      cases hfrv : (((runOf p ms).mv t).src.val == f)
      · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ (hzfr f hfi), hefr f hfi, hfrv]; rfl)
      · cases htov : (((runOf p ms).mv t).dst.val == h)
        · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [lit_neg_eval _ _ (hzto h hhi), heto h hhi, htov]; rfl)
        · cases hmpv : (kindIdx qk == P)
          · exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
              (by rw [lit_neg_eval _ _ (hzmp P (by decide)), hemp P (by decide), hmpv]; rfl)
          · cases hxvv : (code (((runOf p ms).pos t).board (toSq h)) == EMP)
            · exact X13.clause_true
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ List.mem_cons_self)))
                (by
                  rw [lit_neg_eval _ _ (hzx h hhi EMP (by decide)), hex h hhi EMP (by decide), hxvv]
                  rfl)
            · exfalso
              have hqp : qk = .pawn := X13.kindIdx_eq_P qk (beq_iff_eq.mp hmpv)
              have hpsrc : ((runOf p ms).pos t).board ((runOf p ms).mv t).src =
                  some ⟨colorOf (t % 2), .pawn⟩ := by
                rw [hqsrc, hqcc, hqp]
              have e1 : ((runOf p ms).mv t).src.val = f := beq_iff_eq.mp hfrv
              have e2 : ((runOf p ms).mv t).dst.val = h := beq_iff_eq.mp htov
              have hfxne : fx ((runOf p ms).mv t).src ≠ fx ((runOf p ms).mv t).dst := by
                rw [fx_sq, fx_sq, e1, e2]
                exact hfl
              obtain ⟨hcp1, hcp2⟩ := core_pawn hch t ht hpsrc
              have hbnh : ((runOf p ms).pos t).board (toSq h) = none :=
                X13.board_none_of_code_emp _ (beq_iff_eq.mp hxvv)
              rw [← e2, toSq_val] at hbnh
              obtain ⟨v0, hv0, hv0val⟩ := (hcp2 hfxne).resolve_left (fun hne => hne hbnh)
              rw [e2] at hv0val
              have hv0val' : v0.val = sqOf (fl h) (rk h - pdir ((cfgOf w b n m).col t)) := hv0val
              obtain ⟨e, he⟩ := core_epr hch t ht v0 hv0
              have hkeys : v0.val ∈ (((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1)) := by
                have hro : ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) =
                    (eprSquares (cfgOf w b n m) t
                      ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t [])).map (·.1) :=
                  (roles_EPR (cfgOf w b n m) t ht).1
                rw [hro]
                exact List.mem_map.mpr ⟨(v0.val, e), he, rfl⟩
              obtain ⟨v', hv'⟩ := X13.exists_look_of_keys hkeys
              rw [hv0val'] at hv'
              rw [hvlook] at hv'
              cases hv'

theorem fam_cap : FamOK w b n m .cap := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_flatMap, List.mem_range] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
  have hecap : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
      ((encodeCfg (cfgOf w b n m)).layout.ply t).CAP =
      isCapture ((runOf p ms).pos t) ((runOf p ms).mv t) :=
    lit_pos _ _ _ _ (roles_CAPPROMO (cfgOf w b n m) t ht).1
  have hzcap : ((encodeCfg (cfgOf w b n m)).layout.ply t).CAP ≠ 0 := by
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).CAP :=
      (roles_CAPPROMO (cfgOf w b n m) t ht).1.1
    omega
  have heto : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
  have hzto : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).2.1
    omega
  have hex : ∀ s ∈ (cfgOf w b n m).NK, ∀ k, k < 11 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k) =
        (code (((runOf p ms).pos t).board (toSq s)) == k) :=
    fun s hs k hk => lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t s k (Nat.le_of_lt ht) hs hk)
  have hzx : ∀ s ∈ (cfgOf w b n m).NK, ∀ k, k < 11 →
      xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) s k ≠ 0 := by
    intro s hs k hk
    show xv (((encodeCfg (cfgOf w b n m)).layout.X.getD t #[])) s k ≠ 0
    have h0 : 0 < xv (((encodeCfg (cfgOf w b n m)).layout.X.getD t #[])) s k :=
      (roles_X (cfgOf w b n m) t s k (Nat.le_of_lt ht) hs hk).1
    omega
  have hepr : ∀ r v, (r, v) ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) v =
        (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq r)) :=
    fun r v hmem => lit_pos _ _ _ _ ((roles_EPR (cfgOf w b n m) t ht).2 _ hmem)
  have hzpr : ∀ r v, (r, v) ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR → v ≠ 0 := by
    intro r v hmem
    have h0 : 0 < v := ((roles_EPR (cfgOf w b n m) t ht).2 _ hmem).1
    omega
  rcases X14b.mem_plyCapCls (cfgOf w b n m) _ _ _ hfm with ⟨h', hh', hcl⟩ | hb
  · rcases hcl with hcl | hcl
    · rw [hcl]
      cases hdst : (((runOf p ms).mv t).dst.val == h')
      · exact X13.clause_true List.mem_cons_self
          (by rw [lit_neg_eval _ _ (hzto h' hh'), heto h' hh', hdst]; rfl)
      · have hdst' : ((runOf p ms).mv t).dst.val = h' := beq_iff_eq.mp hdst
        have hdts : toSq h' = ((runOf p ms).mv t).dst := by rw [← hdst', toSq_val]
        cases hbc : (code (((runOf p ms).pos t).board (toSq h')) == EMP)
        · have hbd : ((runOf p ms).pos t).board ((runOf p ms).mv t).dst ≠ none := by
            intro hh
            rw [← hdts] at hh
            rw [hh] at hbc
            exact absurd hbc (by decide)
          obtain ⟨qq, hqq⟩ := Option.ne_none_iff_exists'.mp hbd
          have hc2 : ((((runOf p ms).pos t).board ((runOf p ms).mv t).dst).isSome ||
              (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t)).isSome) = true :=
            (Bool.or_eq_true _ _).mpr (Or.inl (by rw [hqq]; rfl))
          have hcap : isCapture ((runOf p ms).pos t) ((runOf p ms).mv t) = true := hc2
          exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            (by rw [hecap]; exact hcap)
        · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [hex h' hh' EMP (by decide)]; exact hbc)
    · rw [hcl]
      cases hcv : isCapture ((runOf p ms).pos t) ((runOf p ms).mv t)
      · exact X13.clause_true (List.mem_append_left _ List.mem_cons_self)
          (by rw [lit_neg_eval _ _ hzcap, hecap, hcv]; rfl)
      · cases hdst : (((runOf p ms).mv t).dst.val == h')
        · exact X13.clause_true (List.mem_append_left _
            (List.mem_cons_of_mem _ List.mem_cons_self))
            (by rw [lit_neg_eval _ _ (hzto h' hh'), heto h' hh', hdst]; rfl)
        · have hdst' : ((runOf p ms).mv t).dst.val = h' := beq_iff_eq.mp hdst
          have hdts : toSq h' = ((runOf p ms).mv t).dst := by rw [← hdst', toSq_val]
          cases hbc : (code (((runOf p ms).pos t).board (toSq h')) == EMP)
          · exact X13.clause_true (List.mem_append_left _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
              (by rw [lit_neg_eval _ _ (hzx h' hh' EMP (by decide)), hex h' hh' EMP (by decide), hbc]; rfl)
          · have hbnone : ((runOf p ms).pos t).board (toSq h') = none :=
              X13.board_none_of_code_emp _ (beq_iff_eq.mp hbc)
            rw [hdts] at hbnone
            have hcapi : ((((runOf p ms).pos t).board ((runOf p ms).mv t).dst).isSome ||
                (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t)).isSome) = true := hcv
            rcases (Bool.or_eq_true _ _).mp hcapi with hl | hr
            · rw [hbnone] at hl
              exact absurd hl (by decide)
            · obtain ⟨v0, hv0⟩ := Option.isSome_iff_exists.mp hr
              obtain ⟨e, he⟩ := core_epr hch t ht v0 hv0
              have hkeys : v0.val ∈ (((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1)) := by
                have hro : ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) =
                    (eprSquares (cfgOf w b n m) t
                      ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t [])).map (·.1) :=
                  (roles_EPR (cfgOf w b n m) t ht).1
                rw [hro]
                exact List.mem_map.mpr ⟨(v0.val, e), he, rfl⟩
              obtain ⟨v', hv'⟩ := X13.exists_look_of_keys hkeys
              have hmemv : v' ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.2) :=
                List.mem_map.mpr ⟨(v0.val, v'), X13.mem_of_look hv', rfl⟩
              exact X13.clause_true (List.mem_append_right _ hmemv)
                (by
                  refine (hepr _ _ (X13.mem_of_look hv')).trans ?_
                  rw [hv0, toSq_val]
                  exact beq_self_eq_true _)
  · obtain ⟨r, v, hrv, he⟩ := hb
    rw [he]
    cases hvictim : (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq r))
    · exact X13.clause_true List.mem_cons_self
        (by rw [lit_neg_eval _ _ (hzpr r v hrv), hepr r v hrv, hvictim]; rfl)
    · have hc2 : ((((runOf p ms).pos t).board ((runOf p ms).mv t).dst).isSome ||
          (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t)).isSome) = true :=
        (Bool.or_eq_true _ _).mpr (Or.inr (by
          rw [show epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some (toSq r) from
            beq_iff_eq.mp hvictim]; rfl))
      have hcap : isCapture ((runOf p ms).pos t) ((runOf p ms).mv t) = true := hc2
      exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self) (by rw [hecap]; exact hcap)



theorem fam_promo : FamOK w b n m .promo := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_flatMap, List.mem_range] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
  obtain ⟨⟨qc, qk⟩, hqsrc, hqcol, hpiece⟩ := legal_nonking_mem _ _ hleg hkm
  have hturn := run_turn hch t (Nat.le_of_lt ht)
  have hqcc : qc = colorOf (t % 2) := hqcol.trans hturn
  have heto : ∀ s ∈ (cfgOf w b n m).NK,
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
    fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
  have hzto : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) ≠ 0 := by
    intro s hs
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to s :=
      (roles_FRTO (cfgOf w b n m) t s ht hs).2.1
    omega
  have hepro : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
      ((encodeCfg (cfgOf w b n m)).layout.ply t).PROMO =
      (((runOf p ms).mv t).promo.isSome : Bool) :=
    lit_pos _ _ _ _ (roles_CAPPROMO (cfgOf w b n m) t ht).2
  have hzpro : ((encodeCfg (cfgOf w b n m)).layout.ply t).PROMO ≠ 0 := by
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).PROMO :=
      (roles_CAPPROMO (cfgOf w b n m) t ht).2.1
    omega
  have hemp : ∀ k, k < 5 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).mp k) = (kindIdx qk == k) := by
    intro k hk
    refine (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).1).trans ?_
    show (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any (fun x => kindIdx x.kind == k) =
      (kindIdx qk == k)
    rw [hqsrc]
    rfl
  have hzmp : ∀ k, k < 5 → (((encodeCfg (cfgOf w b n m)).layout.ply t).mp k) ≠ 0 := by
    intro k hk
    show ((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD k 0 ≠ 0
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).MP.getD k 0 :=
      ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).1.1
    omega
  have hert : ∀ k, k < 5 →
      Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).rt k) =
        (kindIdx (((runOf p ms).mv t).promo.getD qk) == k) := by
    intro k hk
    refine (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).2).trans ?_
    show (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any
        (fun x => kindIdx (((runOf p ms).mv t).promo.getD x.kind) == k) =
      (kindIdx (((runOf p ms).mv t).promo.getD qk) == k)
    rw [hqsrc]
    rfl
  have hzrt : ∀ k, k < 5 → (((encodeCfg (cfgOf w b n m)).layout.ply t).rt k) ≠ 0 := by
    intro k hk
    show ((encodeCfg (cfgOf w b n m)).layout.ply t).RT.getD k 0 ≠ 0
    have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).RT.getD k 0 :=
      ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).2.1
    omega
  have hpawn_of_promo : ((runOf p ms).mv t).promo.isSome = true → qk = .pawn := by
    intro hpr
    by_cases hkp : qk = .pawn
    · exact hkp
    · exfalso
      obtain ⟨-, hpn, -⟩ := mem_pieceMoves_nonpawn _ _ ⟨qc, qk⟩ _ hpiece hkp
      rw [hpn] at hpr
      exact absurd hpr (by decide)
  rcases X14b.mem_plyPromoCls (cfgOf w b n m) t _ _ hfm with h1' | h2' | ⟨l, hlt, h3'⟩ |
    ⟨p0, hp0, h4' | h5'⟩ | h6'
  · rw [h1']
    cases hpr : (((runOf p ms).mv t).promo.isSome)
    · exact X13.clause_true List.mem_cons_self
        (by rw [lit_neg_eval _ _ hzpro, hepro, hpr]; rfl)
    · have hqp := hpawn_of_promo hpr
      exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
        (by rw [hemp P (by decide), hqp]; rfl)
  · rw [h2']
    cases hpr : (((runOf p ms).mv t).promo.isSome)
    · exact X13.clause_true List.mem_cons_self
        (by rw [lit_neg_eval _ _ hzpro, hepro, hpr]; rfl)
    · have hqp := hpawn_of_promo hpr
      have hdNK := (core_src_dst hch t ht).2
      have hpm : ((runOf p ms).mv t) ∈ pawnMoves ((runOf p ms).pos t) ((runOf p ms).mv t).src qc := by
        rw [show (⟨qc, qk⟩ : Piece) = ⟨qc, .pawn⟩ from by rw [hqp]] at hpiece
        exact hpiece
      obtain ⟨-, -, h3⟩ := pawnMoves_cases _ _ _ _ hpm
      have hrylast : ry ((runOf p ms).mv t).dst = ↑(qc.last) := h3.mp hpr
      have hclast : (rk ((runOf p ms).mv t).dst.val ==
          (if (cfgOf w b n m).col t = 0 then (7 : Int) else 0)) = true := by
        rcases color_parity (t % 2) (Nat.mod_lt _ (by decide)) with ⟨he, hcolw, -⟩ | ⟨he, hcolb, -⟩
        · have hq7 : qc.last = 7 := by rw [hqcc, hcolw]; rfl
          have hli : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
          have hco : (cfgOf w b n m).col t = 0 := he
          rw [ite_eq_left hco]
          apply beq_iff_eq.mpr
          omega
        · have hq0 : qc.last = 0 := by rw [hqcc, hcolb]; rfl
          have hli : rk ((runOf p ms).mv t).dst.val = ry ((runOf p ms).mv t).dst := rfl
          have hco : (cfgOf w b n m).col t = 1 := by
            show t % 2 = 1
            exact he
          rw [ite_eq_right (by rw [hco]; decide)]
          apply beq_iff_eq.mpr
          omega
      have hmemlt : ((encodeCfg (cfgOf w b n m)).layout.ply t).to ((runOf p ms).mv t).dst.val ∈
          ((cfgOf w b n m).NK.filter
            fun h' => rk h' == (if (cfgOf w b n m).col t = 0 then (7 : Int) else 0)).map
            ((encodeCfg (cfgOf w b n m)).layout.ply t).to :=
        List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hdNK, hclast⟩, rfl⟩
      exact X13.clause_true (List.mem_cons_of_mem _ hmemlt)
        (by rw [heto _ hdNK]; exact beq_self_eq_true _)
  · rw [h3']
    obtain ⟨h', hh', hto⟩ := List.mem_map.mp hlt
    rw [← hto]
    have hNK' : h' ∈ (cfgOf w b n m).NK := (List.mem_filter.mp hh').1
    have hcond : (rk h' == (if (cfgOf w b n m).col t = 0 then (7 : Int) else 0)) = true :=
      (List.mem_filter.mp hh').2
    cases hmpv : (kindIdx qk == P)
    · exact X13.clause_true List.mem_cons_self
        (by rw [lit_neg_eval _ _ (hzmp P (by decide)), hemp P (by decide), hmpv]; rfl)
    · have hqp : qk = .pawn := X13.kindIdx_eq_P qk (beq_iff_eq.mp hmpv)
      cases htv : (((runOf p ms).mv t).dst.val == h')
      · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by rw [lit_neg_eval _ _ (hzto h' hNK'), heto h' hNK', htv]; rfl)
      · have hpm : ((runOf p ms).mv t) ∈ pawnMoves ((runOf p ms).pos t) ((runOf p ms).mv t).src qc := by
          rw [show (⟨qc, qk⟩ : Piece) = ⟨qc, .pawn⟩ from by rw [hqp]] at hpiece
          exact hpiece
        obtain ⟨-, -, h3⟩ := pawnMoves_cases _ _ _ _ hpm
        have hdstv : ((runOf p ms).mv t).dst.val = h' := beq_iff_eq.mp htv
        have hrylast : ry ((runOf p ms).mv t).dst = ↑(qc.last) := by
          have hli : ry ((runOf p ms).mv t).dst = rk h' := by
            have h1 : ry ((runOf p ms).mv t).dst = rk ((runOf p ms).mv t).dst.val := rfl
            rw [hdstv] at h1
            exact h1
          have hcon : rk h' = (if (cfgOf w b n m).col t = 0 then (7 : Int) else 0) :=
            beq_iff_eq.mp hcond
          rcases color_parity (t % 2) (Nat.mod_lt _ (by decide)) with ⟨he, hcolw, -⟩ | ⟨he, hcolb, -⟩
          · have hq7 : qc.last = 7 := by rw [hqcc, hcolw]; rfl
            have hco : (cfgOf w b n m).col t = 0 := he
            rw [ite_eq_left hco] at hcon
            omega
          · have hq0 : qc.last = 0 := by rw [hqcc, hcolb]; rfl
            have hco : (cfgOf w b n m).col t = 1 := by
              show t % 2 = 1
              exact he
            rw [ite_eq_right (by rw [hco]; decide)] at hcon
            omega
        have hpro : (((runOf p ms).mv t).promo.isSome) = true := h3.mpr hrylast
        exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (by rw [hepro]; exact hpro)
  · rw [h4']
    cases hpr : (((runOf p ms).mv t).promo)
    · cases hmm : (kindIdx qk == p0)
      · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by rw [lit_neg_eval _ _ (hzmp p0 hp0), hemp p0 hp0, hmm]; rfl)
      · exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (by rw [hert p0 hp0, hpr]; exact hmm)
    · exact X13.clause_true List.mem_cons_self (by rw [hepro, hpr]; rfl)
  · rw [h5']
    cases hpr : (((runOf p ms).mv t).promo)
    · cases hmm : (kindIdx qk == p0)
      · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by rw [lit_neg_eval _ _ (hzrt p0 hp0), hert p0 hp0, hpr, Option.getD_none, hmm]; rfl)
      · exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (by rw [hemp p0 hp0]; exact hmm)
    · exact X13.clause_true List.mem_cons_self (by rw [hepro, hpr]; rfl)
  · rw [h6']
    cases hpr : (((runOf p ms).mv t).promo)
    · exact X13.clause_true List.mem_cons_self
        (by rw [lit_neg_eval _ _ hzpro, hepro, hpr]; rfl)
    · rename_i k'
      have hqp := hpawn_of_promo (by rw [hpr]; rfl)
      have hpm : ((runOf p ms).mv t) ∈ pawnMoves ((runOf p ms).pos t) ((runOf p ms).mv t).src qc := by
        rw [show (⟨qc, qk⟩ : Piece) = ⟨qc, .pawn⟩ from by rw [hqp]] at hpiece
        exact hpiece
      have hki := X14b.pawnMoves_promo_kindIdx _ _ _ _ hpm k' hpr
      exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
        (by rw [lit_neg_eval _ _ (hzrt P (by decide)), hert P (by decide), hpr, Option.getD_some,
          show (kindIdx k' == P) = false from (beq_eq_false_iff_ne.mpr hki)]; rfl)



theorem fam_update : FamOK w b n m .update := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_flatMap, List.mem_range] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
  obtain ⟨i, hi1, hi2, hdisj⟩ := mem_plyFrameCls (cfgOf w b n m) c t _ _ _ hfm
  dsimp only at hdisj
  rcases hdisj with hu | hfr
  · obtain ⟨-, hm⟩ := mem_tag _ Fam.update _ hu
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hm
    have hsNK : ((cfgOf w b n m).NK.getD i 0) ∈ (cfgOf w b n m).NK := getD_mem _ _ _ hi1
    obtain ⟨⟨qc, qk⟩, hqsrc, hqcol, hpiece⟩ := legal_nonking_mem _ _ hleg hkm
    have hturn := run_turn hch t (Nat.le_of_lt ht)
    have hefr : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).fr ((cfgOf w b n m).NK.getD i 0)) = (((runOf p ms).mv t).src.val == ((cfgOf w b n m).NK.getD i 0)) :=
      lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t ((cfgOf w b n m).NK.getD i 0) ht hsNK).1
    have hzfr : (((encodeCfg (cfgOf w b n m)).layout.ply t).fr ((cfgOf w b n m).NK.getD i 0)) ≠ 0 := by
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).fr ((cfgOf w b n m).NK.getD i 0) := (roles_FRTO (cfgOf w b n m) t ((cfgOf w b n m).NK.getD i 0) ht hsNK).1.1
      omega
    have heto : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        (((encodeCfg (cfgOf w b n m)).layout.ply t).to ((cfgOf w b n m).NK.getD i 0)) = (((runOf p ms).mv t).dst.val == ((cfgOf w b n m).NK.getD i 0)) :=
      lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t ((cfgOf w b n m).NK.getD i 0) ht hsNK).2
    have hzto : (((encodeCfg (cfgOf w b n m)).layout.ply t).to ((cfgOf w b n m).NK.getD i 0)) ≠ 0 := by
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to ((cfgOf w b n m).NK.getD i 0) := (roles_FRTO (cfgOf w b n m) t ((cfgOf w b n m).NK.getD i 0) ht hsNK).2.1
      omega
    have hert : ∀ k, k < 5 →
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).rt k) =
          (kindIdx (((runOf p ms).mv t).promo.getD qk) == k) := by
      intro k hk
      refine (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).2).trans ?_
      show (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any
          (fun x => kindIdx (((runOf p ms).mv t).promo.getD x.kind) == k) =
        (kindIdx (((runOf p ms).mv t).promo.getD qk) == k)
      rw [hqsrc]
      rfl
    have hzrt : ∀ k, k < 5 → (((encodeCfg (cfgOf w b n m)).layout.ply t).rt k) ≠ 0 := by
      intro k hk
      show ((encodeCfg (cfgOf w b n m)).layout.ply t).RT.getD k 0 ≠ 0
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).RT.getD k 0 := ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).2.1
      omega
    have heX1 : ∀ k, k < 11 →
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (xv ((encodeCfg (cfgOf w b n m)).layout.X0 (t + 1)) ((cfgOf w b n m).NK.getD i 0) k) =
          (code (((runOf p ms).pos (t + 1)).board (toSq ((cfgOf w b n m).NK.getD i 0))) == k) :=
      fun k hk => lit_pos _ _ _ _ (roles_X (cfgOf w b n m) (t + 1) ((cfgOf w b n m).NK.getD i 0) k (by omega) hsNK hk)
    have hzx1 : ∀ k, k < 11 → xv ((encodeCfg (cfgOf w b n m)).layout.X0 (t + 1)) ((cfgOf w b n m).NK.getD i 0) k ≠ 0 := by
      intro k hk
      show xv ((encodeCfg (cfgOf w b n m)).layout.X.getD (t + 1) #[]) ((cfgOf w b n m).NK.getD i 0) k ≠ 0
      have h0 : 0 < xv ((encodeCfg (cfgOf w b n m)).layout.X.getD (t + 1) #[]) ((cfgOf w b n m).NK.getD i 0) k :=
        (roles_X (cfgOf w b n m) (t + 1) ((cfgOf w b n m).NK.getD i 0) k (by omega) hsNK hk).1
      omega
    have hqk : qk ≠ .king := by
      have h1' : (qk == .king) = false := by simpa [isKingMove, hqsrc] using hkm
      intro e
      rw [e] at h1'
      simp at h1'
    have hpnek : (((runOf p ms).mv t).promo ≠ some .king) :=
      promo_ne_king _ _ (legal_mem_pseudo _ _ hleg)
    have hqci : colIdx qc = (cfgOf w b n m).col t := by
      rw [show (cfgOf w b n m).col t = t % 2 from rfl,
        show qc = colorOf (t % 2) from hqcol.trans hturn]
      exact X13.colIdx_colorOf _ (Nat.mod_lt _ (by decide))
    rcases hm with hm | ⟨p0, hp0, hcl⟩
    · rw [hm]
      cases hfrv : (((runOf p ms).mv t).src.val == ((cfgOf w b n m).NK.getD i 0))
      · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzfr, hefr, hfrv]; rfl)
      · have hsrcv : ((runOf p ms).mv t).src.val = ((cfgOf w b n m).NK.getD i 0) := beq_iff_eq.mp hfrv
        have hts : toSq ((cfgOf w b n m).NK.getD i 0) = ((runOf p ms).mv t).src := by rw [← hsrcv, toSq_val]
        have hboard : ((runOf p ms).pos (t + 1)).board (toSq ((cfgOf w b n m).NK.getD i 0)) = none := by
          rw [hstep, hts]
          exact play_board_src _ _ (legal_src_ne_dst _ _ hleg)
        exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
          (by rw [heX1 EMP (by decide), hboard]; rfl)
    · rw [← hcl]
      cases htv : (((runOf p ms).mv t).dst.val == ((cfgOf w b n m).NK.getD i 0))
      · exact X13.clause_true List.mem_cons_self (by rw [lit_neg_eval _ _ hzto, heto, htv]; rfl)
      · cases hrtv : (kindIdx (((runOf p ms).mv t).promo.getD qk) == p0)
        · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [lit_neg_eval _ _ (hzrt p0 hp0), hert p0 hp0, hrtv]; rfl)
        · have hdstv : ((runOf p ms).mv t).dst.val = ((cfgOf w b n m).NK.getD i 0) := beq_iff_eq.mp htv
          have hts : toSq ((cfgOf w b n m).NK.getD i 0) = ((runOf p ms).mv t).dst := by rw [← hdstv, toSq_val]
          have hrpk : (((runOf p ms).mv t).promo.getD qk) ≠ .king := by
            cases hpr : ((runOf p ms).mv t).promo
            · rw [Option.getD_none]
              exact hqk
            · rename_i k'
              rw [Option.getD_some]
              intro e
              exact hpnek (by rw [hpr, e])
          have hboard : ((runOf p ms).pos (t + 1)).board (toSq ((cfgOf w b n m).NK.getD i 0)) =
              some ⟨qc, ((runOf p ms).mv t).promo.getD qk⟩ := by
            rw [hstep, hts]
            cases hpr : ((runOf p ms).mv t).promo
            · rw [X14b.play_board_dst_none _ _ hpr, hqsrc, Option.getD_none]
            · rename_i k'
              rw [X14b.play_board_dst_some _ _ _ hpr, hqsrc, Option.map_some, Option.getD_some]
          have hcode : code (some ⟨qc, ((runOf p ms).mv t).promo.getD qk⟩) =
              5 * (cfgOf w b n m).col t + p0 := by
            rw [X13.code_nonking _ _ hrpk, hqci, beq_iff_eq.mp hrtv]
          have hbnd : 5 * (cfgOf w b n m).col t + p0 < 11 := by
            rw [show (cfgOf w b n m).col t = t % 2 from rfl]
            have h1c : t % 2 < 2 := Nat.mod_lt _ (by decide)
            omega
          exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            (by rw [heX1 _ hbnd, hboard, hcode]; exact beq_self_eq_true _)
  · obtain ⟨hf2, -⟩ := mem_tag _ Fam.frame _ hfr
    rw [hf2] at hf
    exact absurd hf (by decide)



theorem fam_frame : FamOK w b n m .frame := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_flatMap, List.mem_range] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
  obtain ⟨i, hi1, hi2, hdisj⟩ := mem_plyFrameCls (cfgOf w b n m) c t _ _ _ hfm
  dsimp only at hdisj
  rcases hdisj with hu | hfr
  · obtain ⟨hf2, -⟩ := mem_tag _ Fam.update _ hu
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨-, hm⟩ := mem_tag _ Fam.frame _ hfr
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append, List.mem_map,
      List.mem_flatMap, List.mem_range, or_assoc] at hm
    have hsNK : ((cfgOf w b n m).NK.getD i 0) ∈ (cfgOf w b n m).NK := getD_mem _ _ _ hi1
    have hs64 : ((cfgOf w b n m).NK.getD i 0) < 64 := by
      have hX := (List.mem_filter.mp hsNK).1
      exact List.mem_range.mp hX
    have hefr : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).fr ((cfgOf w b n m).NK.getD i 0)) = (((runOf p ms).mv t).src.val == ((cfgOf w b n m).NK.getD i 0)) :=
      lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t ((cfgOf w b n m).NK.getD i 0) ht hsNK).1
    have hzfr : (((encodeCfg (cfgOf w b n m)).layout.ply t).fr ((cfgOf w b n m).NK.getD i 0)) ≠ 0 := by
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).fr ((cfgOf w b n m).NK.getD i 0) := (roles_FRTO (cfgOf w b n m) t ((cfgOf w b n m).NK.getD i 0) ht hsNK).1.1
      omega
    have heto : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).to ((cfgOf w b n m).NK.getD i 0)) = (((runOf p ms).mv t).dst.val == ((cfgOf w b n m).NK.getD i 0)) :=
      lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t ((cfgOf w b n m).NK.getD i 0) ht hsNK).2
    have hzto : (((encodeCfg (cfgOf w b n m)).layout.ply t).to ((cfgOf w b n m).NK.getD i 0)) ≠ 0 := by
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to ((cfgOf w b n m).NK.getD i 0) := (roles_FRTO (cfgOf w b n m) t ((cfgOf w b n m).NK.getD i 0) ht hsNK).2.1
      omega
    have hech : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (((encodeCfg (cfgOf w b n m)).layout.ply t).CH.getD i 0) = (((((runOf p ms).mv t).src.val == ((cfgOf w b n m).NK.getD i 0)) || (((runOf p ms).mv t).dst.val == ((cfgOf w b n m).NK.getD i 0))) || (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq ((cfgOf w b n m).NK.getD i 0)))) :=
      lit_pos _ _ _ _ ((roles_CH (cfgOf w b n m) t ht).2 i hi1)
    have hzch : (((encodeCfg (cfgOf w b n m)).layout.ply t).CH.getD i 0) ≠ 0 := by
      have h0 : 0 < (((encodeCfg (cfgOf w b n m)).layout.ply t).CH.getD i 0) := ((roles_CH (cfgOf w b n m) t ht).2 i hi1).1
      omega
    have hepr' : ∀ r v, (r, v) ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR →
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) v = (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq r)) :=
      fun r v hmem => lit_pos _ _ _ _ ((roles_EPR (cfgOf w b n m) t ht).2 _ hmem)
    have heX0 : ∀ k, k < 11 →
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) ((cfgOf w b n m).NK.getD i 0) k) =
          (code (((runOf p ms).pos t).board (toSq ((cfgOf w b n m).NK.getD i 0))) == k) :=
      fun k hk => lit_pos _ _ _ _ (roles_X (cfgOf w b n m) t ((cfgOf w b n m).NK.getD i 0) k (Nat.le_of_lt ht) hsNK hk)
    have hzx0 : ∀ k, k < 11 → xv ((encodeCfg (cfgOf w b n m)).layout.X0 t) ((cfgOf w b n m).NK.getD i 0) k ≠ 0 := by
      intro k hk
      show xv ((encodeCfg (cfgOf w b n m)).layout.X.getD t #[]) ((cfgOf w b n m).NK.getD i 0) k ≠ 0
      have h0 : 0 < xv ((encodeCfg (cfgOf w b n m)).layout.X.getD t #[]) ((cfgOf w b n m).NK.getD i 0) k :=
        (roles_X (cfgOf w b n m) t ((cfgOf w b n m).NK.getD i 0) k (Nat.le_of_lt ht) hsNK hk).1
      omega
    have heX1 : ∀ k, k < 11 →
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) (xv ((encodeCfg (cfgOf w b n m)).layout.X0 (t + 1)) ((cfgOf w b n m).NK.getD i 0) k) =
          (code (((runOf p ms).pos (t + 1)).board (toSq ((cfgOf w b n m).NK.getD i 0))) == k) :=
      fun k hk => lit_pos _ _ _ _ (roles_X (cfgOf w b n m) (t + 1) ((cfgOf w b n m).NK.getD i 0) k (by omega) hsNK hk)
    have hzx1 : ∀ k, k < 11 → xv ((encodeCfg (cfgOf w b n m)).layout.X0 (t + 1)) ((cfgOf w b n m).NK.getD i 0) k ≠ 0 := by
      intro k hk
      show xv ((encodeCfg (cfgOf w b n m)).layout.X.getD (t + 1) #[]) ((cfgOf w b n m).NK.getD i 0) k ≠ 0
      have h0 : 0 < xv ((encodeCfg (cfgOf w b n m)).layout.X.getD (t + 1) #[]) ((cfgOf w b n m).NK.getD i 0) k :=
        (roles_X (cfgOf w b n m) (t + 1) ((cfgOf w b n m).NK.getD i 0) k (by omega) hsNK hk).1
      omega
    rcases hm with hm | ⟨l, hll, heq⟩ | ⟨k, hk, hcd | hcd⟩
    · rw [hm]
      cases hchv : (((((runOf p ms).mv t).src.val == ((cfgOf w b n m).NK.getD i 0)) || (((runOf p ms).mv t).dst.val == ((cfgOf w b n m).NK.getD i 0))) || (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq ((cfgOf w b n m).NK.getD i 0))))
      · exact X13.clause_true List.mem_cons_self
          (by rw [lit_neg_eval _ _ hzch, hech, hchv]; rfl)
      · rcases Bool.or_eq_true_iff.mp hchv with hAB | hC
        · rcases Bool.or_eq_true_iff.mp hAB with hA | hB
          · exact X13.clause_true (List.mem_cons_of_mem _
              (List.mem_append_left _ List.mem_cons_self)) (by rw [hefr]; exact hA)
          · exact X13.clause_true (List.mem_cons_of_mem _
              (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))
              (by rw [heto]; exact hB)
        · have hvic : epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some (toSq ((cfgOf w b n m).NK.getD i 0)) :=
            beq_iff_eq.mp hC
          obtain ⟨e, he⟩ := core_epr hch t ht (toSq ((cfgOf w b n m).NK.getD i 0)) hvic
          have hkeys : ((cfgOf w b n m).NK.getD i 0) ∈ (((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1)) := by
            have hro : ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) =
                (eprSquares (cfgOf w b n m) t
                  ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t [])).map (·.1) :=
              (roles_EPR (cfgOf w b n m) t ht).1
            rw [hro]
            exact List.mem_map.mpr ⟨((toSq ((cfgOf w b n m).NK.getD i 0)).val, e), he, Nat.mod_eq_of_lt hs64⟩
          obtain ⟨v, hv⟩ := X13.exists_look_of_keys hkeys
          have hmemv : (((cfgOf w b n m).NK.getD i 0), v) ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR := X13.mem_of_look hv
          have hlint : v ∈ (look ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR ((cfgOf w b n m).NK.getD i 0)).toList := by
            rw [hv]
            exact List.mem_singleton_self v
          exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_append_right _ hlint))
            (by rw [hepr' _ _ hmemv]; exact hC)
    · rw [← heq]
      rcases hll with rfl | rfl | hlok
      · cases hA : (((runOf p ms).mv t).src.val == ((cfgOf w b n m).NK.getD i 0))
        · exact X13.clause_true List.mem_cons_self
            (by rw [lit_neg_eval _ _ hzfr, hefr, hA]; rfl)
        · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [hech]; exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl hA))))
      · cases hB : (((runOf p ms).mv t).dst.val == ((cfgOf w b n m).NK.getD i 0))
        · exact X13.clause_true List.mem_cons_self
            (by rw [lit_neg_eval _ _ hzto, heto, hB]; rfl)
        · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [hech]; exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr hB))))
      · cases hlk : look ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR ((cfgOf w b n m).NK.getD i 0) with
        | none =>
            rw [hlk] at hlok
            exact absurd hlok List.not_mem_nil
        | some v =>
            rw [hlk] at hlok
            have hlv : l = v := List.mem_singleton.mp hlok
            have hmemv : (((cfgOf w b n m).NK.getD i 0), v) ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR := X13.mem_of_look hlk
            have hzv : v ≠ 0 := by
              have h0 : 0 < v := ((roles_EPR (cfgOf w b n m) t ht).2 _ hmemv).1
              omega
            rw [hlv]
            cases hC : (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq ((cfgOf w b n m).NK.getD i 0)))
            · exact X13.clause_true List.mem_cons_self
                (by rw [lit_neg_eval _ _ hzv, hepr' _ _ hmemv, hC]; rfl)
            · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
                (by rw [hech]; exact Bool.or_eq_true_iff.mpr (Or.inr hC))
    · cases hchv : (((((runOf p ms).mv t).src.val == ((cfgOf w b n m).NK.getD i 0)) || (((runOf p ms).mv t).dst.val == ((cfgOf w b n m).NK.getD i 0))) || (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq ((cfgOf w b n m).NK.getD i 0))))
      · rw [hcd]
        obtain ⟨hAf, hBf, hCf⟩ := X14b.or3_false hchv
        have hne_src : toSq ((cfgOf w b n m).NK.getD i 0) ≠ ((runOf p ms).mv t).src := by
          intro e
          have e1 : ((cfgOf w b n m).NK.getD i 0) % 64 = ((runOf p ms).mv t).src.val := congrArg Fin.val e
          have e2 : ((cfgOf w b n m).NK.getD i 0) = ((runOf p ms).mv t).src.val := by omega
          rw [e2] at hAf
          rw [beq_self_eq_true] at hAf
          cases hAf
        have hne_dst : toSq ((cfgOf w b n m).NK.getD i 0) ≠ ((runOf p ms).mv t).dst := by
          intro e
          have e1 : ((cfgOf w b n m).NK.getD i 0) % 64 = ((runOf p ms).mv t).dst.val := congrArg Fin.val e
          have e2 : ((cfgOf w b n m).NK.getD i 0) = ((runOf p ms).mv t).dst.val := by omega
          rw [e2] at hBf
          rw [beq_self_eq_true] at hBf
          cases hBf
        have hne_ep : ¬(epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some (toSq ((cfgOf w b n m).NK.getD i 0))) := by
          intro e
          rw [e] at hCf
          rw [beq_self_eq_true] at hCf
          cases hCf
        have hboard : ((runOf p ms).pos (t + 1)).board (toSq ((cfgOf w b n m).NK.getD i 0)) =
            ((runOf p ms).pos t).board (toSq ((cfgOf w b n m).NK.getD i 0)) := by
          rw [hstep]
          exact nonking_board_change _ _ hleg hkm _ hne_src hne_dst hne_ep
        cases hb0 : (code (((runOf p ms).pos t).board (toSq ((cfgOf w b n m).NK.getD i 0))) == k)
        · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [lit_neg_eval _ _ (hzx0 k hk), heX0 k hk, hb0]; rfl)
        · exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            (by rw [heX1 k hk, hboard]; exact hb0)
      · rw [hcd]
        exact X13.clause_true List.mem_cons_self (by rw [hech]; exact hchv)
    · cases hchv : (((((runOf p ms).mv t).src.val == ((cfgOf w b n m).NK.getD i 0)) || (((runOf p ms).mv t).dst.val == ((cfgOf w b n m).NK.getD i 0))) || (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq ((cfgOf w b n m).NK.getD i 0))))
      · rw [hcd]
        obtain ⟨hAf, hBf, hCf⟩ := X14b.or3_false hchv
        have hne_src : toSq ((cfgOf w b n m).NK.getD i 0) ≠ ((runOf p ms).mv t).src := by
          intro e
          have e1 : ((cfgOf w b n m).NK.getD i 0) % 64 = ((runOf p ms).mv t).src.val := congrArg Fin.val e
          have e2 : ((cfgOf w b n m).NK.getD i 0) = ((runOf p ms).mv t).src.val := by omega
          rw [e2] at hAf
          rw [beq_self_eq_true] at hAf
          cases hAf
        have hne_dst : toSq ((cfgOf w b n m).NK.getD i 0) ≠ ((runOf p ms).mv t).dst := by
          intro e
          have e1 : ((cfgOf w b n m).NK.getD i 0) % 64 = ((runOf p ms).mv t).dst.val := congrArg Fin.val e
          have e2 : ((cfgOf w b n m).NK.getD i 0) = ((runOf p ms).mv t).dst.val := by omega
          rw [e2] at hBf
          rw [beq_self_eq_true] at hBf
          cases hBf
        have hne_ep : ¬(epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some (toSq ((cfgOf w b n m).NK.getD i 0))) := by
          intro e
          rw [e] at hCf
          rw [beq_self_eq_true] at hCf
          cases hCf
        have hboard : ((runOf p ms).pos (t + 1)).board (toSq ((cfgOf w b n m).NK.getD i 0)) =
            ((runOf p ms).pos t).board (toSq ((cfgOf w b n m).NK.getD i 0)) := by
          rw [hstep]
          exact nonking_board_change _ _ hleg hkm _ hne_src hne_dst hne_ep
        cases hb0 : (code (((runOf p ms).pos t).board (toSq ((cfgOf w b n m).NK.getD i 0))) == k)
        · exact X13.clause_true (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            (by rw [lit_neg_eval _ _ (hzx1 k hk), heX1 k hk, hboard, hb0]; rfl)
        · exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self)
            (by rw [heX0 k hk]; exact hb0)
      · rw [hcd]
        exact X13.clause_true List.mem_cons_self (by rw [hech]; exact hchv)



theorem fam_start : FamOK w b n m .start := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, startPart, List.mem_append] at hfm
  have hc0 := run_c0 hch 0 (Nat.zero_le n)
  rcases hfm with hfm | hfm
  · obtain ⟨-, hm⟩ := mem_tag c .start _ hfm
    simp only [List.mem_flatMap] at hm
    obtain ⟨s, hs, hm⟩ := hm
    obtain ⟨hsNK, hsrk⟩ := List.mem_filter.mp hs
    have hs64 : s < 64 := List.mem_range.mp (List.mem_filter.mp hsNK).1
    have hgd : ry (toSq s) = rk s := ry_toSq s hs64
    have child : ∀ k0 x0 : Nat, x0 < 2 → k0 = 5 * x0 + 0 → k0 < 11 →
        (code (((runOf p ms).pos 0).board (toSq s)) == k0) = false := by
      intro k0 x0 hx0 hk0e hk0b
      rw [beq_eq_false_iff_ne]
      intro hC
      obtain ⟨c', k', hb0, hc0', hk0'⟩ := X13.code_of_eq _ x0 0 hx0 (by decide) (hk0e ▸ hC)
      have hkk : k' = .pawn := by
        cases k' <;> first | rfl | exact absurd hk0' (by decide)
      have hcc : c' = colorOf x0 := X13.eq_colorOf_colIdx c' x0 hx0 hc0'
      subst hkk
      subst hcc
      obtain ⟨hr0', hr7'⟩ := hc0.pawns (toSq s) (colorOf x0) hb0
      rw [hgd] at hr0' hr7'
      rcases (Bool.or_eq_true_iff.mp hsrk) with h0 | h7
      · exact hr0' (beq_iff_eq.mp h0)
      · exact hr7' (beq_iff_eq.mp h7)
    rcases List.mem_cons.mp hm with hm | hm
    · have hrole : HasRole (encodeCfg (cfgOf w b n m))
          (xv ((encodeCfg (cfgOf w b n m)).layout.X0 0) s P) (.sem (Sem.x 0 s P)) :=
        roles_X (cfgOf w b n m) 0 s P (Nat.zero_le n) hsNK (by decide)
      rw [hm, clause_eval₁, lit_neg _ _ _ _ hrole]
      show (!((code (((runOf p ms).pos 0).board (toSq s))) == P)) = true
      rw [child P 0 (by decide) rfl (by decide)]
      rfl
    · have hm := List.mem_singleton.mp hm
      have hrole : HasRole (encodeCfg (cfgOf w b n m))
          (xv ((encodeCfg (cfgOf w b n m)).layout.X0 0) s (5 + P)) (.sem (Sem.x 0 s (5 + P))) :=
        roles_X (cfgOf w b n m) 0 s (5 + P) (Nat.zero_le n) hsNK (by decide)
      rw [hm, clause_eval₁, lit_neg _ _ _ _ hrole]
      show (!((code (((runOf p ms).pos 0).board (toSq s))) == (5 + P))) = true
      rw [child (5 + P) 1 (by decide) rfl (by decide)]
      rfl
  · obtain ⟨-, hm⟩ := mem_tag c .start _ hfm
    simp only [List.mem_map] at hm
    obtain ⟨⟨qs, a⟩, hqa, hm⟩ := hm
    rw [show ((encodeCfg (cfgOf w b n m)).layout.att 0 1).A =
        ((encodeCfg (cfgOf w b n m)).layout.att 0 1).entries.map (fun e => (e.s, e.a)) from rfl] at hqa
    obtain ⟨en, hen, hpq⟩ := List.mem_map.mp hqa
    rw [Prod.mk.injEq] at hpq
    obtain ⟨h1p, rfl⟩ := hpq
    obtain ⟨cs0, hcs0, hA, _⟩ := (roles_entries (cfgOf w b n m) 0 1 (Nat.zero_le n)
        (by decide)).2 en
        (show en ∈ (attAtL (cfgOf w b n m) 0 1).entries from hen)
    have hkb0 : kingAt ((runOf p ms).pos 0) .black b := hch.2.2.2.1
    have hturn0 : ((runOf p ms).pos 0).turn = .white := hch.2.1
    have hsafe : inCheck ((runOf p ms).pos 0) .black = false := by
      have hsf := hc0.safe
      rw [hturn0] at hsf
      exact hsf
    have hval : (Sem.att 0 1 en.s).val (cfgOf w b n m) (runOf p ms) = false := by
      by_cases hv : (Sem.att 0 1 en.s).val (cfgOf w b n m) (runOf p ms) = true
      · obtain ⟨q, hbq, hqc, hmem⟩ :=
          (core_att_iff_checker hch 0 1 (Nat.zero_le n) (by decide) en.s).mp hv
        have hatt : attacked ((runOf p ms).pos 0).board (toSq ((cfgOf w b n m).K 1)) .white :=
          (attacked_iff _ _ _).mpr ⟨toSq en.s, q, hbq, hqc, hmem⟩
        have hchk : inCheck ((runOf p ms).pos 0) .black = true :=
          (inCheck_iff _ _).mpr ⟨toSq ((cfgOf w b n m).K 1),
            X12.kingAtC0 _ _ _ _ _ hch.2.2.1 hkb0 1 (by decide), hatt⟩
        rw [hchk] at hsafe
        exact absurd hsafe (by decide)
      · cases hvc : (Sem.att 0 1 en.s).val (cfgOf w b n m) (runOf p ms)
        · rfl
        · exact absurd hvc hv
    rw [← hm]
    show Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) [-en.a] = true
    rw [clause_eval₁, lit_neg _ _ _ _ hA]
    show (!(Sem.att 0 1 en.s).val (cfgOf w b n m) (runOf p ms)) = true
    rw [hval]
    rfl


set_option maxHeartbeats 2000000 in
theorem fam_check : FamOK w b n m .check := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, List.mem_append] at hfm
  have h1g : 1 ≤ (cfgOf w b n m).n := h1
  have h64w : (cfgOf w b n m).kw < 64 := w.isLt
  have h64b : (cfgOf w b n m).kb < 64 := b.isLt
  rcases hfm with h0 | hp
  · rw [chk0Part, ite_eq_left h1g] at h0
    obtain ⟨-, hm⟩ := mem_tag c .check _ h0
    apply amo_sound _ _ _ (((encodeCfg (cfgOf w b n m)).layout.att 0 0).entries.map fun en =>
        (Sem.att 0 0 en.s).val (cfgOf w b n m) (runOf p ms)) _ _ _ _ _ _ hm
    · intro l hl
      rw [X12.Amap2] at hl
      obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hl
      obtain ⟨cs0, hcs0, hA, _⟩ := (roles_entries (cfgOf w b n m) 0 0 (Nat.zero_le n)
          (by decide)).2 en
        (show en ∈ (attAtL (cfgOf w b n m) 0 0).entries from hen)
      have h0' := hA.1
      omega
    · intro l hl
      obtain ⟨i, hi, hget⟩ := X13.mem_getD' 0 hl
      rw [← hget]
      have h0' := ((roles_L0 (cfgOf w b n m) h1g).2 i hi).1
      omega
    · rw [X12.Amap2]
      exact X12.fa2_attA w b n m p ms 0 0 (Nat.zero_le n) (by decide)
    · show (((attAtL (cfgOf w b n m) 0 0).entries.map fun en =>
          (Sem.att 0 0 en.s).val (cfgOf w b n m) (runOf p ms)).filter id).length ≤ 1
      exact X12.hamo_att w b n m p ms hch 0 h1g 0 (by decide) rfl
    · intro h8
      have hA8 : 8 < (attAtL (cfgOf w b n m) 0 0).A.length := by
        have h8' : 8 < ((attAtL (cfgOf w b n m) 0 0).A.map (·.2)).length := h8
        rwa [List.length_map] at h8'
      constructor
      · have h2 := (roles_L0 (cfgOf w b n m) h1g).1 hA8
        show (encodeCfg (cfgOf w b n m)).layout.L0.length =
          (((encodeCfg (cfgOf w b n m)).layout.att 0 0).A.map (·.2)).length - 1
        rw [List.length_map]
        exact h2
      · intro i hi
        refine (lit_pos _ _ _ _ ((roles_L0 (cfgOf w b n m) h1g).2 i hi)).trans ?_
        rw [X12.Amapatt]
        exact X12.take_any_congr (cfgOf w b n m) (runOf p ms) (fun en : AttEntry => Sem.att 0 0 en.s)
          (fun en : AttEntry => (Sem.att 0 0 en.s).val (cfgOf w b n m) (runOf p ms)) _ (i + 1)
          fun en _ => rfl
  · simp only [perPart, List.mem_flatMap, List.mem_range, List.mem_append, or_assoc] at hp
    obtain ⟨t, ht, hp⟩ := hp
    have ht' : t < n := by
      have ht0 : t < (cfgOf w b n m).n := ht
      simp only [cfgOf] at ht0
      exact ht0
    have ht1 : t + 1 ≤ n := by omega
    obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht'
    have hkg : (cfgOf w b n m).col t = t % 2 := rfl
    have he : (cfgOf w b n m).col t < 2 := Nat.mod_lt _ (by decide)
    have hee : 1 - (cfgOf w b n m).col t < 2 := by omega
    have ht1le : t + 1 ≤ (cfgOf w b n m).n := ht1
    have hgc2 : inCheck ((runOf p ms).pos (t + 1)) (colorOf (1 - (cfgOf w b n m).col t)) = true := by
      have h2 : inCheck (play ((runOf p ms).pos t) ((runOf p ms).mv t)) ((runOf p ms).pos t).turn.opp =
          true := hgc
      rw [← hstep] at h2
      rw [run_turn hch t (Nat.le_of_lt ht')] at h2
      rw [← X12.opp_colorOf (t % 2) (Nat.mod_lt _ (by decide))] at h2
      rw [hkg]
      exact h2
    have keysE := (roles_entries (cfgOf w b n m) (t + 1) (1 - (cfgOf w b n m).col t) ht1le hee).1
    rcases hp with hp | hp | hp
    · obtain ⟨hf2, -⟩ := mem_tag c .legal _ hp
      rw [hf2] at hf
      exact absurd hf (by decide)
    · obtain ⟨-, hm⟩ := mem_tag c .check _ hp
      rw [List.mem_singleton.mp hm]
      obtain ⟨k', hkk', hatt'⟩ := (inCheck_iff _ _).mp hgc2
      obtain ⟨hkw1, hkb1, hkAll⟩ := run_kings hch (t + 1) ht1
      have hk'2 : k' = toSq ((cfgOf w b n m).K (1 - (cfgOf w b n m).col t)) :=
        X12.kingSqK w b n m _ hkAll hkw1 hkb1 _ hee k' hkk'
      rw [hk'2] at hatt'
      obtain ⟨t0, q0, hb0, hqc0, hmem0⟩ := (attacked_iff _ _ _).mp hatt'
      have hqc2 : q0.color = colorOf (1 - (1 - (cfgOf w b n m).col t)) := by
        have e1 : (colorOf (1 - (cfgOf w b n m).col t)).opp =
            colorOf (1 - (1 - (cfgOf w b n m).col t)) := (X12.opp_colorOf _ hee).symm
        exact hqc0.trans e1
      have hval1 : (Sem.att (t + 1) (1 - (cfgOf w b n m).col t) t0.val).val (cfgOf w b n m)
          (runOf p ms) = true :=
        (core_att_iff_checker hch (t + 1) (1 - (cfgOf w b n m).col t) ht1le hee t0.val).mpr
          ⟨q0, by rw [toSq_val]; exact hb0, hqc2, by rw [toSq_val]; exact hmem0⟩
      obtain ⟨cs0, hcs0, conj0, hconj0, hv0⟩ :=
        core_att_complete hch (t + 1) (1 - (cfgOf w b n m).col t) ht1le hee t0.val t0.isLt hval1
      obtain ⟨en, hen, henS⟩ := List.mem_map.mp (show t0.val ∈
          (attAtL (cfgOf w b n m) (t + 1) (1 - (cfgOf w b n m).col t)).entries.map (·.s) from by
        rw [keysE]
        exact List.mem_map.mpr ⟨(t0.val, cs0), hcs0, rfl⟩)
      obtain ⟨csx, hcsx, hA, _⟩ := (roles_entries (cfgOf w b n m) (t + 1)
        (1 - (cfgOf w b n m).col t) ht1le hee).2 en hen
      have ev : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) en.a = true := by
        have ev0 := lit_pos (encodeCfg (cfgOf w b n m)) (runOf p ms) en.a _ hA
        rw [henS] at ev0
        exact ev0.trans hval1
      rw [X12.Amap2]
      exact X13.clause_true (List.mem_map.mpr ⟨en,
        (show en ∈ ((encodeCfg (cfgOf w b n m)).layout.att (t + 1) (1 - (cfgOf w b n m).col t)).entries
          from hen), rfl⟩) ev
    · obtain ⟨hspl, hp⟩ := X12.perPart_tail (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout t c hp
      obtain ⟨-, hm⟩ := mem_tag c .check _ hp
      have hspl' : t + 1 ≤ n - 1 := hspl
      have ht1lt : t + 1 < n := by omega
      apply amo_sound _ _ _ (((encodeCfg (cfgOf w b n m)).layout.att (t + 1)
          (1 - (cfgOf w b n m).col t)).entries.map fun en =>
        (Sem.att (t + 1) (1 - (cfgOf w b n m).col t) en.s).val (cfgOf w b n m) (runOf p ms))
        _ _ _ _ _ _ hm
      · intro l hl
        rw [X12.Amap2] at hl
        obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hl
        obtain ⟨cs0, hcs0, hA, _⟩ := (roles_entries (cfgOf w b n m) (t + 1)
            (1 - (cfgOf w b n m).col t) ht1le hee).2 en
          (show en ∈ (attAtL (cfgOf w b n m) (t + 1) (1 - (cfgOf w b n m).col t)).entries from hen)
        have h0' := hA.1
        omega
      · intro l hl
        obtain ⟨i, hi, hget⟩ := X13.mem_getD' 0 hl
        rw [← hget]
        have h0' := ((roles_LS (cfgOf w b n m) t
            (show t + 1 ≤ (cfgOf w b n m).n - 1 from hspl')).2 i hi).1
        omega
      · rw [X12.Amap2]
        exact X12.fa2_attA w b n m p ms (t + 1) (1 - (cfgOf w b n m).col t) ht1le hee
      · show (((attAtL (cfgOf w b n m) (t + 1) (1 - (cfgOf w b n m).col t)).entries.map fun en =>
            (Sem.att (t + 1) (1 - (cfgOf w b n m).col t) en.s).val (cfgOf w b n m)
            (runOf p ms)).filter id).length ≤ 1
        exact X12.hamo_att w b n m p ms hch (t + 1) ht1lt (1 - (cfgOf w b n m).col t) hee (by
          rw [hkg]; omega)
      · intro h8
        have hA8 : 8 < (attAtL (cfgOf w b n m) (t + 1) (1 - (cfgOf w b n m).col t)).A.length := by
          have h8' : 8 < ((attAtL (cfgOf w b n m) (t + 1) (1 - (cfgOf w b n m).col t)).A.map
              (·.2)).length := h8
          rwa [List.length_map] at h8'
        constructor
        · have h2 := (roles_LS (cfgOf w b n m) t
              (show t + 1 ≤ (cfgOf w b n m).n - 1 from hspl')).1 hA8
          show ((encodeCfg (cfgOf w b n m)).layout.LS.getD t []).length =
            (((encodeCfg (cfgOf w b n m)).layout.att (t + 1) (1 - (cfgOf w b n m).col t)).A.map
              (·.2)).length - 1
          rw [List.length_map]
          exact h2
        · intro i hi
          refine (lit_pos _ _ _ _ ((roles_LS (cfgOf w b n m) t
              (show t + 1 ≤ (cfgOf w b n m).n - 1 from hspl')).2 i hi)).trans ?_
          rw [X12.Amapatt]
          exact X12.take_any_congr (cfgOf w b n m) (runOf p ms)
            (fun en : AttEntry => Sem.att (t + 1) (1 - (cfgOf w b n m).col t) en.s)
            (fun en : AttEntry =>
              (Sem.att (t + 1) (1 - (cfgOf w b n m).col t) en.s).val (cfgOf w b n m) (runOf p ms))
            _ (i + 1) fun en _ => rfl


theorem fam_legal : FamOK w b n m .legal := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc, perPart, List.mem_flatMap, List.mem_range, List.mem_append, or_assoc] at hfm
  obtain ⟨t, ht, hfm⟩ := hfm
  have ht' : t < n := by
    have ht0 : t < (cfgOf w b n m).n := ht
    simp only [cfgOf] at ht0
    exact ht0
  obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht'
  have ht1 : t + 1 ≤ n := by omega
  have hturnC : ((runOf p ms).pos t).turn = colorOf ((cfgOf w b n m).col t) := run_turn hch t (Nat.le_of_lt ht')
  obtain ⟨hkw1, hkb1, -⟩ := run_kings hch (t + 1) ht1
  have hsafe0 : inCheck ((runOf p ms).pos (t + 1)) (colorOf ((cfgOf w b n m).col t)) = false := by
    have hls := legal_safe _ _ hleg
    rw [← hstep] at hls
    rw [hturnC] at hls
    exact hls
  have hc02 : (cfgOf w b n m).col t < 2 := Nat.mod_lt _ (by decide)
  rcases hfm with hfm | hfm | hfm
  · obtain ⟨-, hm⟩ := mem_tag c .legal _ hfm
    simp only [List.mem_map] at hm
    obtain ⟨⟨qs, a⟩, hqa, hm⟩ := hm
    rw [show ((encodeCfg (cfgOf w b n m)).layout.att (t + 1) ((cfgOf w b n m).col t)).A =
        ((encodeCfg (cfgOf w b n m)).layout.att (t + 1) ((cfgOf w b n m).col t)).entries.map
          (fun e => (e.s, e.a)) from rfl] at hqa
    obtain ⟨en, hen, hpq⟩ := List.mem_map.mp hqa
    rw [Prod.mk.injEq] at hpq
    obtain ⟨h1p, rfl⟩ := hpq
    obtain ⟨cs0, hcs0, hA, _⟩ := (roles_entries (cfgOf w b n m) (t + 1) ((cfgOf w b n m).col t) ht1
        hc02).2 en
        (show en ∈ (attAtL (cfgOf w b n m) (t + 1) ((cfgOf w b n m).col t)).entries from hen)
    have hval : (Sem.att (t + 1) ((cfgOf w b n m).col t) en.s).val (cfgOf w b n m) (runOf p ms) =
        false := by
      by_cases hv : (Sem.att (t + 1) ((cfgOf w b n m).col t) en.s).val (cfgOf w b n m) (runOf p ms) =
          true
      · obtain ⟨q, hbq, hqc, hmem⟩ :=
          (core_att_iff_checker hch (t + 1) ((cfgOf w b n m).col t) ht1 hc02 en.s).mp hv
        have hqc2 : q.color = (colorOf ((cfgOf w b n m).col t)).opp := by
          rw [← X12.opp_colorOf ((cfgOf w b n m).col t) hc02]
          exact hqc
        have hatt : attacked ((runOf p ms).pos (t + 1)).board
            (toSq ((cfgOf w b n m).K ((cfgOf w b n m).col t)))
            (colorOf ((cfgOf w b n m).col t)).opp :=
          (attacked_iff _ _ _).mpr ⟨toSq en.s, q, hbq, hqc2, hmem⟩
        have hchk : inCheck ((runOf p ms).pos (t + 1)) (colorOf ((cfgOf w b n m).col t)) = true :=
          (inCheck_iff _ _).mpr ⟨toSq ((cfgOf w b n m).K ((cfgOf w b n m).col t)),
            X12.kingAtC0 w b n m _ hkw1 hkb1 ((cfgOf w b n m).col t) hc02, hatt⟩
        rw [hchk] at hsafe0
        exact absurd hsafe0 (by decide)
      · cases hvc : (Sem.att (t + 1) ((cfgOf w b n m).col t) en.s).val (cfgOf w b n m) (runOf p ms)
        · rfl
        · exact absurd hvc hv
    rw [← hm]
    show Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) [-en.a] = true
    rw [clause_eval₁, lit_neg _ _ _ _ hA]
    show (!(Sem.att (t + 1) ((cfgOf w b n m).col t) en.s).val (cfgOf w b n m) (runOf p ms)) = true
    rw [hval]
    rfl
  · obtain ⟨hf2, -⟩ := mem_tag c .check _ hfm
    rw [hf2] at hf
    exact absurd hf (by decide)
  · obtain ⟨hspl, hfm⟩ := X12.perPart_tail (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout t c hfm
    obtain ⟨hf2, -⟩ := mem_tag c .check _ hfm
    rw [hf2] at hf
    exact absurd hf (by decide)


theorem fam_capcount : FamOK w b n m .capcount := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  obtain ⟨hc0, hturn0, hkw, hkb, hkf, hlen, hcaps⟩ := hch
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc] at hfm
  unfold capsPart at hfm
  obtain ⟨-, hmm⟩ := mem_tag _ Fam.capcount _ hfm
  have hlenCL : ((((encodeCfg (cfgOf w b n m)).layout.PL.toList).map (·.CAP))).length = n := by
    rw [List.length_map, Array.length_toList, PL_size]
    rfl
  have hne : (((encodeCfg (cfgOf w b n m)).layout.PL.toList).map (·.CAP)) ≠ [] := by
    intro e
    have e2 := congrArg List.length e
    rw [List.length_nil] at e2
    rw [hlenCL] at e2
    omega
  have hz : ∀ c0 ∈ (((encodeCfg (cfgOf w b n m)).layout.PL.toList).map (·.CAP)), c0 ≠ 0 := by
    intro c0 hc0
    obtain ⟨q0, hq0, hq2⟩ := List.mem_map.mp hc0
    obtain ⟨i, hi, hget⟩ := X13.mem_getD' default hq0
    rw [Array.length_toList, PL_size] at hi
    have hget2 : (encodeCfg (cfgOf w b n m)).layout.PL.getD i default = q0 := by
      rw [← hget]
      exact (X14b.getD_toList (encodeCfg (cfgOf w b n m)).layout.PL i default).symm
    have hpos : 0 < q0.CAP := by
      rw [← hget2]
      show 0 < ((encodeCfg (cfgOf w b n m)).layout.ply i).CAP
      exact (roles_CAPPROMO (cfgOf w b n m) i hi).1.1
    omega
  have hzS : ∀ r ∈ ((encodeCfg (cfgOf w b n m)).layout.S.toList), ∀ l ∈ r, l ≠ 0 := by
    by_cases hm0 : (cfgOf w b n m).m = 0
    · intro r hr
      rw [X14b.S_empty' (cfgOf w b n m) h1 hm0] at hr
      exact absurd hr List.not_mem_nil
    · intro r hr
      obtain ⟨i, hi, hget⟩ := X13.mem_getD' ([] : List Int) hr
      have hSL : (((encodeCfg (cfgOf w b n m)).layout.S.toList)).length = (cfgOf w b n m).n := by
        rw [Array.length_toList, (roles_S (cfgOf w b n m) h1 hm0).1]
      have hi' : i < (cfgOf w b n m).n := by omega
      intro l hl
      rw [← hget, X14b.getD_toList (encodeCfg (cfgOf w b n m)).layout.S i []] at hl
      obtain ⟨j, hj, hget2⟩ := X13.mem_getD' (0 : Int) hl
      have hrowlen := ((roles_S (cfgOf w b n m) h1 hm0).2 i hi').1
      have hj' : j < (cfgOf w b n m).m + 1 := by rw [hrowlen] at hj; exact hj
      have hpos := ((roles_S (cfgOf w b n m) h1 hm0).2 i hi').2 j hj' |>.1
      rw [hget2] at hpos
      omega
  have hl : Fa2 (fun l v => Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) l = v) (((encodeCfg (cfgOf w b n m)).layout.PL.toList).map (·.CAP)) ((List.range n).map fun t => isCapture ((runOf p ms).pos t) ((runOf p ms).mv t)) := by
    have hCAPs : (((encodeCfg (cfgOf w b n m)).layout.PL.toList).map (·.CAP)) = (List.range n).map
        fun t => ((encodeCfg (cfgOf w b n m)).layout.ply t).CAP := by
      have e := X13.list_eq_range_getD (0 : Int) (((encodeCfg (cfgOf w b n m)).layout.PL.toList).map (·.CAP))
      rw [hlenCL] at e
      rw [e]
      apply List.map_congr_left
      intro a ha
      have han : a < n := List.mem_range.mp ha
      exact caps_layout (cfgOf w b n m) a han
    rw [hCAPs]
    refine X13.fa2_map_of _ _ (fun t => isCapture ((runOf p ms).pos t) ((runOf p ms).mv t)) _ ?_
    intro t htn
    show Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) ((encodeCfg (cfgOf w b n m)).layout.ply t).CAP = _
    exact lit_pos _ _ _ _ (roles_CAPPROMO (cfgOf w b n m) t (List.mem_range.mp htn)).1
  have hcaps2 : caps p ms ≤ (cfgOf w b n m).m := hcaps
  have hm : (((List.range n).map fun t => isCapture ((runOf p ms).pos t) ((runOf p ms).mv t)).filter id).length ≤ (cfgOf w b n m).m := by
    calc (((List.range n).map fun t => isCapture ((runOf p ms).pos t) ((runOf p ms).mv t)).filter id).length
        = (((List.range ms.length).map
            fun t => isCapture ((runOf p ms).pos t) ((runOf p ms).mv t)).filter id).length := by
          rw [hlen]
      _ = caps p ms := (X14b.caps_eq_cnt p ms).symm
      _ ≤ (cfgOf w b n m).m := hcaps2
  have hS : (cfgOf w b n m).m ≠ 0 →
      (((encodeCfg (cfgOf w b n m)).layout.S.toList).length = (((encodeCfg (cfgOf w b n m)).layout.PL.toList).map (·.CAP)).length ∧
        ∀ i, i < (((encodeCfg (cfgOf w b n m)).layout.PL.toList).map (·.CAP)).length → ((((encodeCfg (cfgOf w b n m)).layout.S.toList)).getD i []).length = (cfgOf w b n m).m + 1 ∧
          ∀ j, j < (cfgOf w b n m).m + 1 →
            Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) ((((encodeCfg (cfgOf w b n m)).layout.S.toList).getD i []).getD j 0) =
              decide (j + 1 ≤ ((((List.range n).map fun t => isCapture ((runOf p ms).pos t) ((runOf p ms).mv t)).take (i + 1)).filter id).length)) := by
    intro hm0
    obtain ⟨hsl, hsr⟩ := roles_S (cfgOf w b n m) h1 hm0
    refine ⟨?_, fun i hi => ?_⟩
    · rw [Array.length_toList, hsl, hlenCL]
      rfl
    · have hin : i < (cfgOf w b n m).n := by
        rw [← hlenCL]
        exact hi
      obtain ⟨hrow, hrole⟩ := hsr i hin
      constructor
      · rw [X14b.getD_toList ((encodeCfg (cfgOf w b n m)).layout.S) i []]
        exact hrow
      · intro j hj
        rw [X14b.getD_toList ((encodeCfg (cfgOf w b n m)).layout.S) i []]
        refine (lit_pos _ _ _ _ (hrole j hj)).trans ?_
        show decide (j + 1 ≤ (((((List.range (cfgOf w b n m).n).map Sem.cap).take (i + 1)).filter
            fun a => Sem.val (encodeCfg (cfgOf w b n m)).cfg (runOf p ms) a)).length) = _
        exact congrArg (fun A => decide (j + 1 ≤ A))
          (X14b.take_cnt_map_sem (encodeCfg (cfgOf w b n m)).cfg (runOf p ms) Sem.cap
            (fun t => isCapture ((runOf p ms).pos t) ((runOf p ms).mv t)) (List.range n) (i + 1)
            fun s hs => rfl)
  exact counter_sound _ (cfgOf w b n m) _ _ _ hne hz hzS hl hm hS c.1 hmm



theorem ray_mem_NK (g : Cfg) (x : Nat) (hx : x < 2) (hw : g.kw < 64) (hb : g.kb < 64)
    (d : Int × Int) (hd : d ∈ orth ++ diag) (s : Nat) (hs : s ∈ g.ray x d) : s ∈ g.NK := by
  obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hs
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hK : g.K x < 64 := by rcases hx01 with rfl | rfl; exact hw; exact hb
  obtain ⟨h64, hf, hr⟩ := ray_getD g x d hd hK j hj
  have e0 : (g.ray x d).getD j 0 = s := (List.getElem_eq_getD 0).symm.trans hjv
  have h64s : s < 64 := e0 ▸ h64
  have hne1 : s ≠ g.K x := by
    intro he
    rw [e0] at hf hr
    have hf2 : fl s = fl (g.K x) := congrArg fl he
    have hr2 : rk s = rk (g.K x) := congrArg rk he
    have z1 : ((j : Int) + 1) * d.1 = 0 := by omega
    have z2 : ((j : Int) + 1) * d.2 = 0 := by omega
    rcases Int.mul_eq_zero.mp z1 with hz | hdz1
    · omega
    · rcases Int.mul_eq_zero.mp z2 with hz | hdz2
      · omega
      · rcases mem_orth_diag_ne d hd with h1n | h2n
        · exact absurd hdz1 h1n
        · exact absurd hdz2 h2n
  have hne2 : s ≠ g.K (1 - x) := by
    have h2 := go_ne_o d (g.K (1 - x)) 8 (fl (g.K x) + d.1) (rk (g.K x) + d.2) s
      (by rw [← ray_eq_go]; exact hs)
    exact h2
  have hnew : s ≠ g.kw := by
    rcases hx01 with rfl | rfl
    · exact hne1
    · exact hne2
  have hneb : s ≠ g.kb := by
    rcases hx01 with rfl | rfl
    · exact hne2
    · exact hne1
  refine List.mem_filter.mpr ⟨List.mem_range.mpr h64s, ?_⟩
  show (!((s == g.kw) || (s == g.kb))) = true
  rw [beq_eq_false_iff_ne.mpr hnew, beq_eq_false_iff_ne.mpr hneb]
  rfl

theorem npList_key (g : Cfg) (x : Nat) (s0 : Nat) (p : Nat × List ALit) (hp : p ∈ npList g x s0) :
    p.1 = s0 := by
  have hp0 : (p.1, p.2) ∈ npList g x s0 := hp
  rcases (np_list_mem g x s0 p.1 p.2).mp hp0 with ⟨_, h, -⟩ | ⟨_, h, -⟩ <;> exact h

theorem pieceList_key (g : Cfg) (x : Nat) (d : Int × Int) (j : Nat) (p : Nat × List ALit)
    (hp : p ∈ pieceList g x d j) : p.1 = (g.ray x d).getD j 0 := by
  rcases List.mem_cons.mp hp with h | h
  · exact (Prod.ext_iff.mp h).1
  · exact (Prod.ext_iff.mp (List.mem_singleton.mp h)).1

theorem insertKeys_keys_NK (g : Cfg) :
    ∀ (ks : List (Nat × List ALit)), (∀ p ∈ ks, p.1 ∈ g.NK) →
    ∀ (al0 : List (Nat × List (List ALit))), (∀ p ∈ al0, p.1 ∈ g.NK) →
    ∀ p, p ∈ insertKeys ks al0 → p.1 ∈ g.NK := by
  intro ks
  induction ks with
  | nil => intro _ al0 hal p hp; exact hal p hp
  | cons p' ks ih =>
    intro hks al0 hal q hq
    rw [show insertKeys (p' :: ks) al0 = insertKeys ks (insertAlt al0 p'.1 p'.2) from by
      simp only [insertKeys, List.foldl_cons]] at hq
    refine ih (fun r hr => hks r (List.mem_cons_of_mem _ hr)) _ ?_ q hq
    intro r hr
    have hmem : r.1 ∈ (insertAlt al0 p'.1 p'.2).map (·.1) := List.mem_map.mpr ⟨r, hr, rfl⟩
    rw [insertAlt_keys] at hmem
    by_cases hany : (al0.any fun y => (y.1 == p'.1)) = true
    · rw [if_pos hany] at hmem
      obtain ⟨u, hu, hue⟩ := List.mem_map.mp hmem
      rw [← hue]
      exact hal u hu
    · rw [if_neg hany] at hmem
      rcases List.mem_append.mp hmem with h1 | h2
      · obtain ⟨u, hu, hue⟩ := List.mem_map.mp h1
        rw [← hue]
        exact hal u hu
      · rw [List.mem_singleton.mp h2]
        exact hks p' List.mem_cons_self

theorem attAlts_key_NK (g : Cfg) (x : Nat) (hx : x < 2) (hw : g.kw < 64) (hb : g.kb < 64)
    (s : Nat) (cs : List (List ALit)) (h : (s, cs) ∈ attAlts g x) : s ∈ g.NK := by
  have hks : ∀ p ∈ g.NK.flatMap (npList g x) ++ (orth ++ diag).flatMap (dirList g x), p.1 ∈ g.NK := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨s0, hs0, hp'⟩ := List.mem_flatMap.mp hp
      rw [npList_key g x s0 p hp']
      exact hs0
    · obtain ⟨d, hd, hp'⟩ := List.mem_flatMap.mp hp
      obtain ⟨j, hj, hp''⟩ := List.mem_flatMap.mp hp'
      rw [pieceList_key g x d j p hp'']
      exact ray_mem_NK g x hx hw hb d hd _ (getD_mem _ 0 j (List.mem_range.mp hj))
  rw [attAlts_eq_keys] at h
  exact insertKeys_keys_NK g _ hks _ (fun p hp => absurd hp List.not_mem_nil) _ h

theorem fam_r1 : FamOK w b n m .r1 := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc] at hfm
  obtain ⟨t, ht, hfm⟩ := redundant_mem (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hfm
  rcases hfm with hfm | hfm | hfm | hfm
  · obtain ⟨-, hfm⟩ := hfm
    obtain ⟨hsNK, hdNK⟩ := core_src_dst hch t ht
    have hct : (cfgOf w b n m).col t = t % 2 := rfl
    have he2 : 1 - (cfgOf w b n m).col t < 2 := by rw [hct]; have h2 := Nat.mod_lt t (show 0 < 2 by decide); omega
    have ht1 : t + 1 ≤ (cfgOf w b n m).n := ht
    have hK64 : (cfgOf w b n m).K (1 - t % 2) < 64 := by
      have h2 : t % 2 < 2 := Nat.mod_lt _ (show 0 < 2 by decide)
      rcases (by omega : 1 - t % 2 = 0 ∨ 1 - t % 2 = 1) with h0 | h0
      · rw [Cfg.K, if_pos h0]; exact w.isLt
      · rw [Cfg.K, if_neg (by omega)]; exact b.isLt
    have hefr : ∀ s ∈ (cfgOf w b n m).NK,
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
          (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) = (((runOf p ms).mv t).src.val == s) :=
      fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).1
    have heto : ∀ s ∈ (cfgOf w b n m).NK,
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
          (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
      fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
    simp only [r1Cls, AttLayer.A, List.mem_map] at hfm
    obtain ⟨⟨qs, a⟩, ⟨en, hen, hpa⟩, hcl⟩ := hfm
    injection hpa with hseq haeq
    obtain ⟨cs0, hcs0, hrole, -⟩ :=
      (roles_entries (cfgOf w b n m) (t + 1) (1 - (cfgOf w b n m).col t) ht1 he2).2 en hen
    have hrole2 : HasRole (encodeCfg (cfgOf w b n m)) a
        (.sem (.att (t + 1) (1 - (cfgOf w b n m).col t) qs)) := by
      rw [← haeq, ← hseq]
      exact hrole
    have hqsatt : (qs, cs0) ∈ attAlts (cfgOf w b n m) (1 - (cfgOf w b n m).col t) := by
      rw [← hseq]
      exact hcs0
    have hqsNK : qs ∈ (cfgOf w b n m).NK := attAlts_key_NK _ _ he2 w.isLt b.isLt _ _ hqsatt
    have hqs64 : qs < 64 := X5.NK_lt _ _ hqsNK
    have hane : a ≠ 0 := by have h0 := hrole2.1; omega
    have haeval : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) a =
        (Sem.att (t + 1) (1 - (cfgOf w b n m).col t) qs).val (cfgOf w b n m) (runOf p ms) :=
      lit_pos _ _ _ _ hrole2
    rw [← hcl]
    show Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
      ([-a, ((encodeCfg (cfgOf w b n m)).layout.ply t).to qs] ++
          (btw qs ((cfgOf w b n m).K (1 - (cfgOf w b n m).col t))).map
            ((encodeCfg (cfgOf w b n m)).layout.ply t).fr ++
        (btw qs ((cfgOf w b n m).K (1 - (cfgOf w b n m).col t))).filterMap
          fun s => look ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR s) = true
    cases hav : (Sem.att (t + 1) (1 - (cfgOf w b n m).col t) qs).val (cfgOf w b n m) (runOf p ms)
    · exact X13.clause_true (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl List.mem_cons_self))))
        (by rw [lit_neg_eval _ _ hane, haeval, hav]; rfl)
    · obtain ⟨pc, hboard, hcol, hatt⟩ :=
        (core_att_iff_checker hch (t + 1) (1 - (cfgOf w b n m).col t) ht1 he2 qs).mp hav
      have hc' : pc.color = colorOf (t % 2) := by
        rw [hcol, hct]
        congr 1
        have h2 := Nat.mod_lt t (show 0 < 2 by decide)
        omega
      obtain hdst | ⟨z, hin, hz⟩ := core_r1 hch t ht (toSq qs) pc hboard hc' hatt
      · have hqseq : qs = ((runOf p ms).mv t).dst.val := by
          have e0 := congrArg (fun s : Sq => s.val) hdst
          rw [show (toSq qs).val = qs % 64 from rfl, Nat.mod_eq_of_lt hqs64] at e0
          exact e0
        exact X13.clause_true
          (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
            (List.mem_cons_of_mem _ List.mem_cons_self)))))
          (by rw [heto qs hqsNK, hqseq]; exact beq_self_eq_true _)
      · have hbt : z.val ∈ btw qs ((cfgOf w b n m).K (1 - (cfgOf w b n m).col t)) := by
          have h0 := (mem_btw_iff_nat (toSq qs) (toSq ((cfgOf w b n m).K (1 - t % 2))) z.val).mpr
            ⟨z.isLt, by rw [toSq_val]; exact hin⟩
          rw [show (toSq qs).val = qs % 64 from rfl, Nat.mod_eq_of_lt hqs64,
            show (toSq ((cfgOf w b n m).K (1 - t % 2))).val =
              (cfgOf w b n m).K (1 - t % 2) % 64 from rfl,
            Nat.mod_eq_of_lt hK64] at h0
          exact h0
        rcases hz with rfl | hepv
        · exact X13.clause_true
            (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
              (List.mem_map.mpr ⟨_, hbt, rfl⟩)))))
            (by rw [hefr _ hsNK]; exact beq_self_eq_true _)
        · obtain ⟨e0, he0⟩ := core_epr hch t ht z hepv
          have hro : ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) =
              (eprSquares (cfgOf w b n m) t
                ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t [])).map (·.1) :=
            (roles_EPR (cfgOf w b n m) t ht).1
          have hkeys : z.val ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) := by
            rw [hro]
            exact List.mem_map.mpr ⟨(z.val, e0), he0, rfl⟩
          obtain ⟨v', hv'⟩ := X13.exists_look_of_keys hkeys
          have hrole3 := (roles_EPR (cfgOf w b n m) t ht).2 _ (X13.mem_of_look hv')
          exact X13.clause_true
            (List.mem_append.mpr (Or.inr (List.mem_filterMap.mpr ⟨z.val, hbt, hv'⟩)))
            (by
              refine (lit_pos _ _ _ _ hrole3).trans ?_
              show (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq z.val)) = true
              rw [hepv, toSq_val]
              exact beq_self_eq_true _)
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)

theorem fam_r2 : FamOK w b n m .r2 := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc] at hfm
  obtain ⟨t, ht, hfm⟩ := redundant_mem (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hfm
  rcases hfm with hfm | hfm | hfm | hfm
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)
  · obtain ⟨-, hfm⟩ := hfm
    obtain ⟨hsNK, hdNK⟩ := core_src_dst hch t ht
    have hct : (cfgOf w b n m).col t = t % 2 := rfl
    have hc2 : (cfgOf w b n m).col t < 2 := by rw [hct]; exact Nat.mod_lt _ (show 0 < 2 by decide)
    have ht0 : t ≤ (cfgOf w b n m).n := Nat.le_of_lt ht
    have hK64 : (cfgOf w b n m).K (t % 2) < 64 := by
      have h2 : t % 2 < 2 := Nat.mod_lt _ (show 0 < 2 by decide)
      rcases (by omega : t % 2 = 0 ∨ t % 2 = 1) with h0 | h0
      · rw [Cfg.K, if_pos h0]; exact w.isLt
      · rw [Cfg.K, if_neg (by omega)]; exact b.isLt
    have heto : ∀ s ∈ (cfgOf w b n m).NK,
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
          (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
      fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
    have hzto : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) ≠ 0 := by
      intro s hs
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to s :=
        (roles_FRTO (cfgOf w b n m) t s ht hs).2.1
      omega
    simp only [r2Cls, AttLayer.A, List.mem_map] at hfm
    obtain ⟨⟨qs, a⟩, ⟨en, hen, hpa⟩, hcl⟩ := hfm
    injection hpa with hseq haeq
    obtain ⟨cs0, hcs0, hrole, -⟩ :=
      (roles_entries (cfgOf w b n m) t ((cfgOf w b n m).col t) ht0 hc2).2 en hen
    have hrole2 : HasRole (encodeCfg (cfgOf w b n m)) a
        (.sem (.att t ((cfgOf w b n m).col t) qs)) := by
      rw [← haeq, ← hseq]
      exact hrole
    have hqsatt : (qs, cs0) ∈ attAlts (cfgOf w b n m) ((cfgOf w b n m).col t) := by
      rw [← hseq]
      exact hcs0
    have hqsNK : qs ∈ (cfgOf w b n m).NK := attAlts_key_NK _ _ hc2 w.isLt b.isLt _ _ hqsatt
    have hqs64 : qs < 64 := X5.NK_lt _ _ hqsNK
    have hane : a ≠ 0 := by have h0 := hrole2.1; omega
    have haeval : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) a =
        (Sem.att t ((cfgOf w b n m).col t) qs).val (cfgOf w b n m) (runOf p ms) :=
      lit_pos _ _ _ _ hrole2
    rw [← hcl]
    show Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
      ([-a, ((encodeCfg (cfgOf w b n m)).layout.ply t).to qs] ++
          (look ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR qs).toList ++
        (btw qs ((cfgOf w b n m).K ((cfgOf w b n m).col t))).map
          ((encodeCfg (cfgOf w b n m)).layout.ply t).to) = true
    cases hav : (Sem.att t ((cfgOf w b n m).col t) qs).val (cfgOf w b n m) (runOf p ms)
    · exact X13.clause_true (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl List.mem_cons_self))))
        (by rw [lit_neg_eval _ _ hane, haeval, hav]; rfl)
    · obtain ⟨pc, hboard, hcol, hatt⟩ :=
        (core_att_iff_checker hch t ((cfgOf w b n m).col t) ht0 hc2 qs).mp hav
      obtain hdst | hepv | hin := core_r2 hch t ht (toSq qs) pc hboard hcol hatt
      · have hqseq : ((runOf p ms).mv t).dst.val = qs := by
          have e0 := congrArg (fun s : Sq => s.val) hdst
          rw [show (toSq qs).val = qs % 64 from rfl, Nat.mod_eq_of_lt hqs64] at e0
          exact e0
        exact X13.clause_true
          (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
            (List.mem_cons_of_mem _ List.mem_cons_self)))))
          (by rw [heto qs hqsNK, hqseq]; exact beq_self_eq_true _)
      · obtain ⟨e0, he0⟩ := core_epr hch t ht (toSq qs) hepv
        have hro : ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) =
            (eprSquares (cfgOf w b n m) t
              ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t [])).map (·.1) :=
          (roles_EPR (cfgOf w b n m) t ht).1
        have hkeys : (toSq qs).val ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) := by
          rw [hro]
          exact List.mem_map.mpr ⟨((toSq qs).val, e0), he0, rfl⟩
        obtain ⟨v', hv'⟩ := X13.exists_look_of_keys hkeys
        rw [show (toSq qs).val = qs from Nat.mod_eq_of_lt hqs64] at hv'
        have hrole3 := (roles_EPR (cfgOf w b n m) t ht).2 _ (X13.mem_of_look hv')
        exact X13.clause_true
          (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
            (by rw [hv']; exact List.mem_cons_self)))))
          (by
            refine (lit_pos _ _ _ _ hrole3).trans ?_
            show (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq qs)) = true
            rw [hepv]
            exact beq_self_eq_true _)
      · have hbt : ((runOf p ms).mv t).dst.val ∈ btw qs ((cfgOf w b n m).K ((cfgOf w b n m).col t)) := by
          have h0 := (mem_btw_iff_nat (toSq qs) (toSq ((cfgOf w b n m).K (t % 2)))
            ((runOf p ms).mv t).dst.val).mpr
            ⟨((runOf p ms).mv t).dst.isLt, by rw [toSq_val]; exact hin⟩
          rw [show (toSq qs).val = qs % 64 from rfl, Nat.mod_eq_of_lt hqs64,
            show (toSq ((cfgOf w b n m).K (t % 2))).val =
              (cfgOf w b n m).K (t % 2) % 64 from rfl,
            Nat.mod_eq_of_lt hK64] at h0
          exact h0
        exact X13.clause_true
          (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, hbt, rfl⟩)))
          (by rw [heto _ hdNK]; exact beq_self_eq_true _)
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)

theorem fam_r3 : FamOK w b n m .r3 := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc] at hfm
  obtain ⟨t, ht, hfm⟩ := redundant_mem (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hfm
  rcases hfm with hfm | hfm | hfm | hfm
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)
  · obtain ⟨-, hfm⟩ := hfm
    obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
    obtain ⟨hsNK, hdNK⟩ := core_src_dst hch t ht
    have hct : (cfgOf w b n m).col t = t % 2 := rfl
    have heto : ∀ s ∈ (cfgOf w b n m).NK,
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
          (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
      fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
    have hzto : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) ≠ 0 := by
      intro s hs
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to s :=
        (roles_FRTO (cfgOf w b n m) t s ht hs).2.1
      omega
    simp only [r3Cls] at hfm
    rcases Nat.lt_or_ge t 1 with ht1 | ht1
    · rw [if_neg (show ¬(1 ≤ t) from by omega)] at hfm
      exact absurd hfm List.not_mem_nil
    rw [if_pos ht1] at hfm
    obtain ⟨u, hu, hF⟩ := List.mem_filterMap.mp hfm
    change (if (cfgOf w b n m).cand ((cfgOf w b n m).col t) u = true then none
      else match look ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR
          (sqOf (fl u) (rk u - pdir ((cfgOf w b n m).col t))) with
        | some v =>
          if (cfgOf w b n m).cand ((cfgOf w b n m).col t)
              (sqOf (fl u) (rk u - pdir ((cfgOf w b n m).col t))) = true then
            some [-((encodeCfg (cfgOf w b n m)).layout.ply t).to u, v]
          else some [-((encodeCfg (cfgOf w b n m)).layout.ply t).to u]
        | none => some [-((encodeCfg (cfgOf w b n m)).layout.ply t).to u]) = some c.1 at hF
    by_cases hcd : (cfgOf w b n m).cand ((cfgOf w b n m).col t) u = true
    · rw [if_pos hcd] at hF
      cases hF
    rw [if_neg hcd] at hF
    have hcd' : (cfgOf w b n m).cand (t % 2) u = false := Bool.eq_false_iff.mpr hcd
    have epchain : ∀ v0 : Sq, epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) = some v0 →
        ((runOf p ms).mv t).dst.val = u →
        ∃ v', v0.val = sqOf (fl u) (rk u - pdir (t % 2)) ∧
          look ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR
            (sqOf (fl u) (rk u - pdir (t % 2))) = some v' ∧
          Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) v' = true := by
      intro v0 hv0 edh
      have hfn : ((runOf p ms).mv t).src.file ≠ ((runOf p ms).mv t).dst.file := by
        rw [epVictim_eq] at hv0
        by_cases hcc : ((((runOf p ms).pos t).board ((runOf p ms).mv t).src).any
              (·.kind == .pawn) &&
            ((runOf p ms).mv t).src.file != ((runOf p ms).mv t).dst.file &&
            empty ((runOf p ms).pos t).board (((runOf p ms).mv t).dst)) = true
        · rw [if_pos hcc] at hv0
          exact bne_iff_ne.mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hcc).1).2
        · rw [if_neg hcc] at hv0
          cases hv0
      have hfnI : fx ((runOf p ms).mv t).src ≠ fx ((runOf p ms).mv t).dst := by
        intro he
        exact hfn (Int.ofNat_inj.mp he)
      obtain ⟨hepp, hdn0, hvb, hfxv, hryv, hsrcc⟩ := epVictim_spec _ _ _ hleg hv0
      have hpsrc : ((runOf p ms).pos t).board ((runOf p ms).mv t).src =
          some ⟨colorOf (t % 2), .pawn⟩ := by
        rw [← run_turn hch t (Nat.le_of_lt ht)]
        exact hsrcc
      obtain ⟨hcp1, hcp2⟩ := core_pawn hch t ht hpsrc
      rcases hcp2 hfnI with hdn | ⟨v0', hv0', hv0val⟩
      · exact absurd hdn0 hdn
      · have hveq : v0' = v0 := Option.some.inj (hv0'.symm.trans hv0)
        subst v0'
        obtain ⟨e0, he0⟩ := core_epr hch t ht v0 hv0
        have hro : ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) =
            (eprSquares (cfgOf w b n m) t
              ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t [])).map (·.1) :=
          (roles_EPR (cfgOf w b n m) t ht).1
        have hkeys : v0.val ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) := by
          rw [hro]
          exact List.mem_map.mpr ⟨(v0.val, e0), he0, rfl⟩
        obtain ⟨v', hv'⟩ := X13.exists_look_of_keys hkeys
        have hrole3 := (roles_EPR (cfgOf w b n m) t ht).2 _ (X13.mem_of_look hv')
        have hveval : Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms)) v' = true := by
          refine (lit_pos _ _ _ _ hrole3).trans ?_
          show (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq v0.val)) = true
          rw [hv0, toSq_val]
          exact beq_self_eq_true _
        rw [edh] at hv0val
        exact ⟨v', hv0val, by rw [hv0val] at hv'; exact hv', hveval⟩
    split at hF
    · rename_i v hlk
      split at hF
      · rename_i hc2
        have hF2 : c.1 = [-((encodeCfg (cfgOf w b n m)).layout.ply t).to u, v] :=
          (Option.some.inj hF).symm
        rw [hF2]
        cases htv : (((runOf p ms).mv t).dst.val == u)
        · exact X13.clause_true List.mem_cons_self
            (by rw [lit_neg_eval _ _ (hzto u hu), heto u hu, htv]; rfl)
        · have edh : ((runOf p ms).mv t).dst.val = u := beq_iff_eq.mp htv
          obtain hcb | ⟨v0, hv0, hcand0⟩ := core_r3 hch t ht1 ht
          · rw [edh, hcd'] at hcb
            exact absurd hcb (by decide)
          · obtain ⟨v', hv0val, hv', hveval⟩ := epchain v0 hv0 edh
            rw [hct] at hlk
            rw [hlk] at hv'
            obtain hvv := Option.some.inj hv'
            rw [hvv]
            exact X13.clause_true (List.mem_cons_of_mem _ List.mem_cons_self) hveval
      · rename_i hc2
        have hF2 : c.1 = [-((encodeCfg (cfgOf w b n m)).layout.ply t).to u] := (Option.some.inj hF).symm
        rw [hF2]
        cases htv : (((runOf p ms).mv t).dst.val == u)
        · exact X13.clause_true List.mem_cons_self
            (by rw [lit_neg_eval _ _ (hzto u hu), heto u hu, htv]; rfl)
        · have edh : ((runOf p ms).mv t).dst.val = u := beq_iff_eq.mp htv
          obtain hcb | ⟨v0, hv0, hcand0⟩ := core_r3 hch t ht1 ht
          · rw [edh, hcd'] at hcb
            exact absurd hcb (by decide)
          · obtain ⟨v', hv0val, hv', hveval⟩ := epchain v0 hv0 edh
            rw [hv0val] at hcand0
            rw [hct] at hc2
            exact absurd hcand0 hc2
    · rename_i hlk
      have hF2 : c.1 = [-((encodeCfg (cfgOf w b n m)).layout.ply t).to u] := (Option.some.inj hF).symm
      rw [hF2]
      cases htv : (((runOf p ms).mv t).dst.val == u)
      · exact X13.clause_true List.mem_cons_self
          (by rw [lit_neg_eval _ _ (hzto u hu), heto u hu, htv]; rfl)
      · have edh : ((runOf p ms).mv t).dst.val = u := beq_iff_eq.mp htv
        obtain hcb | ⟨v0, hv0, hcand0⟩ := core_r3 hch t ht1 ht
        · rw [edh, hcd'] at hcb
          exact absurd hcb (by decide)
        · obtain ⟨v', hv0val, hv', hveval⟩ := epchain v0 hv0 edh
          rw [hct] at hlk
          rw [hlk] at hv'
          cases hv'

theorem fam_r4 : FamOK w b n m .r4 := by
  intro h1 p ms hch c hc hf
  rw [encode_cfg w b n m] at hc ⊢
  have hfm := mem_famSrc (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hc
  rw [hf] at hfm
  simp only [famSrc] at hfm
  obtain ⟨t, ht, hfm⟩ := redundant_mem (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout c hfm
  rcases hfm with hfm | hfm | hfm | hfm
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)
  · obtain ⟨-, hfm⟩ := hfm
    obtain ⟨hleg, hgc, hkm, hstep⟩ := run_step hch t ht
    obtain ⟨⟨qc, qk⟩, hqsrc, hqcol, hpiece⟩ := legal_nonking_mem _ _ hleg hkm
    obtain ⟨hsNK, hdNK⟩ := core_src_dst hch t ht
    have hct : (cfgOf w b n m).col t = t % 2 := rfl
    have hefr : ∀ s ∈ (cfgOf w b n m).NK,
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
          (((encodeCfg (cfgOf w b n m)).layout.ply t).fr s) = (((runOf p ms).mv t).src.val == s) :=
      fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).1
    have heto : ∀ s ∈ (cfgOf w b n m).NK,
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
          (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) = (((runOf p ms).mv t).dst.val == s) :=
      fun s hs => lit_pos _ _ _ _ (roles_FRTO (cfgOf w b n m) t s ht hs).2
    have hzto : ∀ s ∈ (cfgOf w b n m).NK, (((encodeCfg (cfgOf w b n m)).layout.ply t).to s) ≠ 0 := by
      intro s hs
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).to s :=
        (roles_FRTO (cfgOf w b n m) t s ht hs).2.1
      omega
    have hert : ∀ k, k < 5 →
        Lit.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
          (((encodeCfg (cfgOf w b n m)).layout.ply t).rt k) =
        (kindIdx (((runOf p ms).mv t).promo.getD qk) == k) := by
      intro k hk
      refine (lit_pos _ _ _ _ ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).2).trans ?_
      show (((runOf p ms).pos t).board ((runOf p ms).mv t).src).any
          (fun x => kindIdx (((runOf p ms).mv t).promo.getD x.kind) == k) =
        (kindIdx (((runOf p ms).mv t).promo.getD qk) == k)
      rw [hqsrc]
      rfl
    have hzrt : ∀ k, k < 5 → (((encodeCfg (cfgOf w b n m)).layout.ply t).rt k) ≠ 0 := by
      intro k hk
      show ((encodeCfg (cfgOf w b n m)).layout.ply t).RT.getD k 0 ≠ 0
      have h0 : 0 < ((encodeCfg (cfgOf w b n m)).layout.ply t).RT.getD k 0 :=
        ((roles_MPRT (cfgOf w b n m) t ht).2.2 k hk).2.1
      omega
    simp only [r4Cls, List.mem_flatMap] at hfm
    obtain ⟨u, hu, hfm⟩ := hfm
    obtain ⟨p0, hp0, hF⟩ := List.mem_filterMap.mp hfm
    have hp5 : p0 < 5 := List.mem_range.mp hp0
    change (if !attacksGeom p0 ((cfgOf w b n m).col t) u ((cfgOf w b n m).K (1 - (cfgOf w b n m).col t)) ||
        (btw u ((cfgOf w b n m).K (1 - (cfgOf w b n m).col t))).any (cfgOf w b n m).isK then
      some ([-((encodeCfg (cfgOf w b n m)).layout.ply t).to u,
        -((encodeCfg (cfgOf w b n m)).layout.ply t).rt p0] ++
        discLits (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout t)
      else none) = some c.1 at hF
    by_cases hcond : (!attacksGeom p0 ((cfgOf w b n m).col t) u
        ((cfgOf w b n m).K (1 - (cfgOf w b n m).col t)) ||
        (btw u ((cfgOf w b n m).K (1 - (cfgOf w b n m).col t))).any (cfgOf w b n m).isK) = true
    · rw [if_pos hcond] at hF
      have hF2 : c.1 = [-((encodeCfg (cfgOf w b n m)).layout.ply t).to u,
          -((encodeCfg (cfgOf w b n m)).layout.ply t).rt p0] ++
        discLits (cfgOf w b n m) (encodeCfg (cfgOf w b n m)).layout t := (Option.some.inj hF).symm
      rw [hF2]
      show Clause.eval (intended (encodeCfg (cfgOf w b n m)) (runOf p ms))
        ([-((encodeCfg (cfgOf w b n m)).layout.ply t).to u,
          -((encodeCfg (cfgOf w b n m)).layout.ply t).rt p0] ++
          (((cfgOf w b n m).NK.filter
              ((cfgOf w b n m).raySquares (1 - (cfgOf w b n m).col t)).contains).map
              ((encodeCfg (cfgOf w b n m)).layout.ply t).fr ++
            (((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.filter fun (r, _) =>
                ((cfgOf w b n m).raySquares (1 - (cfgOf w b n m).col t)).contains r).map (·.2))) = true
      cases htv : (((runOf p ms).mv t).dst.val == u)
      · exact X13.clause_true (List.mem_append.mpr (Or.inl List.mem_cons_self))
          (by rw [lit_neg_eval _ _ (hzto u hu), heto u hu, htv]; rfl)
      · have edh : ((runOf p ms).mv t).dst.val = u := beq_iff_eq.mp htv
        cases hkv : (kindIdx (((runOf p ms).mv t).promo.getD qk) == p0)
        · exact X13.clause_true (List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)))
            (by rw [lit_neg_eval _ _ (hzrt p0 hp5), hert p0 hp5, hkv]; rfl)
        · have hpk : kindIdx (((runOf p ms).mv t).promo.getD qk) = p0 := beq_iff_eq.mp hkv
          have hng : attacksGeom p0 (t % 2) ((runOf p ms).mv t).dst.val ((cfgOf w b n m).K (1 - t % 2)) = false ∨
              (btw ((runOf p ms).mv t).dst.val ((cfgOf w b n m).K (1 - t % 2))).any (cfgOf w b n m).isK = true := by
            rw [← edh] at hcond
            rcases (Bool.or_eq_true _ _).mp hcond with h1 | h1
            · left
              cases hag : attacksGeom p0 ((cfgOf w b n m).col t) ((runOf p ms).mv t).dst.val
                ((cfgOf w b n m).K (1 - (cfgOf w b n m).col t)) with
              | false => exact hag
              | true => rw [hag] at h1; exact absurd h1 (by decide)
            · exact Or.inr h1
          obtain hcont | ⟨v0, hv0, hcont⟩ := core_r4 hch t ht p0 ⟨⟨qc, qk⟩, hqsrc, hpk⟩ hng
          · exact X13.clause_true
              (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl
                (List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hsNK, hcont⟩, rfl⟩)))))
              (by rw [hefr _ hsNK]; exact beq_self_eq_true _)
          · obtain ⟨e0, he0⟩ := core_epr hch t ht v0 hv0
            have hro : ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) =
                (eprSquares (cfgOf w b n m) t
                  ((encodeCfg (cfgOf w b n m)).layout.EPS.getD t [])).map (·.1) :=
              (roles_EPR (cfgOf w b n m) t ht).1
            have hkeys : v0.val ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR.map (·.1) := by
              rw [hro]
              exact List.mem_map.mpr ⟨(v0.val, e0), he0, rfl⟩
            obtain ⟨v', hv'⟩ := X13.exists_look_of_keys hkeys
            have hrole3 := (roles_EPR (cfgOf w b n m) t ht).2 _ (X13.mem_of_look hv')
            have hmemE : (v0.val, v') ∈ ((encodeCfg (cfgOf w b n m)).layout.ply t).EPR :=
              X13.mem_of_look hv'
            exact X13.clause_true
              (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
                (List.mem_map.mpr ⟨(v0.val, v'), List.mem_filter.mpr ⟨hmemE, hcont⟩, rfl⟩)))))
              (by
                refine (lit_pos _ _ _ _ hrole3).trans ?_
                show (epVictim ((runOf p ms).pos t) ((runOf p ms).mv t) == some (toSq v0.val)) = true
                rw [hv0, toSq_val]
                exact beq_self_eq_true _)
    · rw [if_neg hcond] at hF
      cases hF
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)
  · obtain ⟨hff, -⟩ := hfm
    rw [hff] at hf
    exact absurd hf (by decide)

theorem famOK_all (fam : Fam) : FamOK w b n m fam := by
  cases fam
  · exact fam_onehot w b n m
  · exact fam_clear w b n m
  · exact fam_attack w b n m
  · exact fam_ep w b n m
  · exact fam_move1 w b n m
  · exact fam_source w b n m
  · exact fam_dest w b n m
  · exact fam_geom w b n m
  · exact fam_transit w b n m
  · exact fam_pawn w b n m
  · exact fam_cap w b n m
  · exact fam_promo w b n m
  · exact fam_update w b n m
  · exact fam_frame w b n m
  · exact fam_start w b n m
  · exact fam_check w b n m
  · exact fam_legal w b n m
  · exact fam_capcount w b n m
  · exact fam_r1 w b n m
  · exact fam_r2 w b n m
  · exact fam_r3 w b n m
  · exact fam_r4 w b n m

theorem encode_sat (h1 : 1 ≤ n) (p : Pos) (ms : List Move) (h : ChainAt w b n m p ms) : Sat (F w b n m) := by
  refine ⟨intended (encode w b n m) (runOf p ms), ?_⟩
  simp only [F, Encoding.formula, Formula.eval, List.all_map, List.all_eq_true, Function.comp_def]
  intro c hc
  exact famOK_all w b n m c.2 h1 p ms h c hc rfl

theorem noChain_of_unsat (h1 : 1 ≤ n) (h : Unsat (F w b n m)) : NoChain w b n m :=
  fun p ms hc => h (encode_sat w b n m h1 p ms hc)

end Families

end Chess.C364.Enc
