import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2838

open PEqualNP.CircuitLowerBounds

def Sup {n : ℕ} (D : Finset (Fin n)) (V : ℕ → (Fin n → Bool) → Bool) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v ∈ D ∧ V i (fun k => decide (k = v)) = true)

def Good {n : ℕ} (D : Finset (Fin n)) (V : ℕ → (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (i : ℕ) : Prop :=
  ∀ x : Fin n → Bool, (∀ v, x v = true → v ∈ D) → V i x = true → ∃ v ∈ S, x v = true

def Cnt {n : ℕ} (D : Finset (Fin n)) {ι : Type} [Fintype ι] (R : ι → Finset (Fin n))
    (V : ℕ → (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ∀ Q : ι → Finset ℕ, (∀ r, ∀ i ∈ Q r, Good D V (R r) i) →
    ∑ r, ((Q r).biUnion (Sup D V)).card ≤ ∑ r, (Q r).card + k

def MonoV {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool) : Prop :=
  ∀ (i : ℕ) (x y : Fin n → Bool), (∀ v, x v = true → y v = true) → V i x = true → V i y = true

lemma good_sub {n : ℕ} (D : Finset (Fin n)) (V : ℕ → (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (i : ℕ) (h : Good D V S i) : Sup D V i ⊆ S := by
  intro v hv
  obtain ⟨hvD, hval⟩ := (Finset.mem_filter.mp hv).2
  obtain ⟨w, hw, hwv⟩ := h _ (fun u hu => by rw [of_decide_eq_true hu]; exact hvD) hval
  have e : w = v := of_decide_eq_true hwv
  exact e ▸ hw

lemma cnt_replace {n : ℕ} (D : Finset (Fin n)) {ι : Type} [Fintype ι] (R : ι → Finset (Fin n))
    (V V' : ℕ → (Fin n → Bool) → Bool) (m k d : ℕ)
    (hne : ∀ i, i ≠ m → V' i = V i) (h : Cnt D R V k)
    (Q' : ι → Finset ℕ) (hQ' : ∀ r, ∀ i ∈ Q' r, Good D V' (R r) i)
    (rep : ι → Finset ℕ) (e : ι → ℕ) (he : ∑ r, e r ≤ d)
    (hrep : ∀ r, m ∈ Q' r → (∀ i ∈ rep r, Good D V (R r) i) ∧
      Sup D V' m ⊆ (rep r).biUnion (Sup D V) ∧ (rep r).card ≤ 1 + e r) :
    ∑ r, ((Q' r).biUnion (Sup D V')).card ≤ ∑ r, (Q' r).card + (k + d) := by
  classical
  have hS : ∀ i, i ≠ m → Sup D V' i = Sup D V i := fun i hi => by
    unfold Sup
    rw [hne i hi]
  have hG : ∀ i, i ≠ m → ∀ S, Good D V' S i → Good D V S i := fun i hi S hg => by
    unfold Good at hg ⊢
    rw [hne i hi] at hg
    exact hg
  have hQ : ∀ r, ∀ i ∈ (if m ∈ Q' r then rep r ∪ (Q' r).erase m else Q' r),
      Good D V (R r) i := by
    intro r i hi
    by_cases hm : m ∈ Q' r
    · rw [if_pos hm] at hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact (hrep r hm).1 i hi
      · obtain ⟨him, hi⟩ := Finset.mem_erase.mp hi
        exact hG i him _ (hQ' r i hi)
    · rw [if_neg hm] at hi
      exact hG i (fun e' => hm (e' ▸ hi)) _ (hQ' r i hi)
  have h1 := h (fun r => if m ∈ Q' r then rep r ∪ (Q' r).erase m else Q' r) hQ
  have hsub : ∀ r, (Q' r).biUnion (Sup D V') ⊆
      (if m ∈ Q' r then rep r ∪ (Q' r).erase m else Q' r).biUnion (Sup D V) := by
    intro r v hv
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    by_cases hm : m ∈ Q' r
    · rw [if_pos hm]
      by_cases him : i = m
      · rw [him] at hvi
        obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp ((hrep r hm).2.1 hvi)
        exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_union_left _ hu, hvu⟩
      · rw [hS i him] at hvi
        exact Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨him, hi⟩), hvi⟩
    · rw [if_neg hm]
      have him : i ≠ m := fun e' => hm (e' ▸ hi)
      rw [hS i him] at hvi
      exact Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩
  have hcard : ∀ r, (if m ∈ Q' r then rep r ∪ (Q' r).erase m else Q' r).card ≤
      (Q' r).card + e r := by
    intro r
    by_cases hm : m ∈ Q' r
    · rw [if_pos hm]
      have a1 := Finset.card_union_le (rep r) ((Q' r).erase m)
      have a2 := Finset.card_erase_of_mem hm
      have a3 := (hrep r hm).2.2
      have a4 : 0 < (Q' r).card := Finset.card_pos.mpr ⟨m, hm⟩
      omega
    · rw [if_neg hm]
      omega
  have s1 : ∑ r, ((Q' r).biUnion (Sup D V')).card ≤
      ∑ r, ((if m ∈ Q' r then rep r ∪ (Q' r).erase m else Q' r).biUnion (Sup D V)).card :=
    Finset.sum_le_sum (fun r _ => Finset.card_le_card (hsub r))
  have s2 : ∑ r, (if m ∈ Q' r then rep r ∪ (Q' r).erase m else Q' r).card ≤
      ∑ r, ((Q' r).card + e r) := Finset.sum_le_sum (fun r _ => hcard r)
  rw [Finset.sum_add_distrib] at s2
  omega

lemma cnt_and {n : ℕ} (D : Finset (Fin n)) {ι : Type} [Fintype ι] (R : ι → Finset (Fin n))
    (V V' : ℕ → (Fin n → Bool) → Bool) (m k : ℕ) (T : Finset ℕ)
    (hne : ∀ i, i ≠ m → V' i = V i)
    (hm : ∀ x, V' m x = true ↔ ∀ u ∈ T, V u x = true) (hmono : MonoV V) (h : Cnt D R V k) :
    Cnt D R V' k := by
  classical
  intro Q' hQ'
  have key : ∀ r, m ∈ Q' r → ∃ u, u ∈ T ∧ Good D V (R r) u := by
    intro r hr
    by_contra hcon
    push_neg at hcon
    have hbad : ∀ u, ∃ x : Fin n → Bool, u ∈ T →
        ((∀ v, x v = true → v ∈ D) ∧ V u x = true ∧ ∀ v ∈ R r, x v = false) := by
      intro u
      by_cases hu : u ∈ T
      · have hb := hcon u hu
        unfold Good at hb
        push_neg at hb
        obtain ⟨x, hx1, hx2, hx3⟩ := hb
        exact ⟨x, fun _ => ⟨hx1, hx2, fun v hv => by simpa using hx3 v hv⟩⟩
      · exact ⟨fun _ => false, fun h' => absurd h' hu⟩
    choose f hf using hbad
    have hz : V' m (fun v => decide (∃ u ∈ T, f u v = true)) = true :=
      (hm _).mpr (fun u hu => hmono u (f u) _
        (fun v hv => decide_eq_true ⟨u, hu, hv⟩) (hf u hu).2.1)
    obtain ⟨v, hv, hzv⟩ := hQ' r m hr _ (fun v hv => by
      obtain ⟨u, hu, huv⟩ := of_decide_eq_true hv
      exact (hf u hu).1 v huv) hz
    obtain ⟨u, hu, huv⟩ := of_decide_eq_true hzv
    have hfv := (hf u hu).2.2 v hv
    rw [hfv] at huv
    exact Bool.noConfusion huv
  choose! g hg using key
  have hfin := cnt_replace D R V V' m k 0 hne h Q' hQ' (fun r => {g r}) (fun _ => 0) (by simp)
    (fun r hr => ⟨fun i hi => by
        rw [Finset.mem_singleton.mp hi]
        exact (hg r hr).2, by
        intro v hv
        rw [Finset.singleton_biUnion]
        obtain ⟨hvD, hval⟩ := (Finset.mem_filter.mp hv).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvD, (hm _).mp hval (g r) (hg r hr).1⟩,
      by simp⟩)
  simpa using hfin

lemma cnt_or {n : ℕ} (D : Finset (Fin n)) {ι : Type} [Fintype ι] (R : ι → Finset (Fin n))
    (hR : ∀ r r', r ≠ r' → ∀ x x', x ∈ R r → x ∈ R r' → x' ∈ R r → x' ∈ R r' → x = x')
    (V V' : ℕ → (Fin n → Bool) → Bool) (m k : ℕ) (T : Finset ℕ) (hT : T.card ≤ 2)
    (hne : ∀ i, i ≠ m → V' i = V i)
    (hm : ∀ x, V' m x = true ↔ ∃ u ∈ T, V u x = true) (h : Cnt D R V k) :
    Cnt D R V' (k + 1) := by
  classical
  intro Q' hQ'
  have hchild : ∀ r, m ∈ Q' r → ∀ u ∈ T, Good D V (R r) u := by
    intro r hr u hu x hx hval
    exact hQ' r m hr x hx ((hm x).mpr ⟨u, hu, hval⟩)
  have hsupm : ∀ v, v ∈ Sup D V' m ↔ ∃ u ∈ T, v ∈ Sup D V u := by
    intro v
    constructor
    · intro hv
      obtain ⟨hvD, hval⟩ := (Finset.mem_filter.mp hv).2
      obtain ⟨u, hu, huv⟩ := (hm _).mp hval
      exact ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvD, huv⟩⟩
    · rintro ⟨u, hu, hv⟩
      obtain ⟨hvD, hval⟩ := (Finset.mem_filter.mp hv).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvD, (hm _).mpr ⟨u, hu, hval⟩⟩
  by_cases hA : ∃ u ∈ T, Sup D V' m ⊆ Sup D V u
  · obtain ⟨u, hu, hsub⟩ := hA
    have hfin := cnt_replace D R V V' m k 0 hne h Q' hQ' (fun _ => {u}) (fun _ => 0) (by simp)
      (fun r hr => ⟨fun i hi => by
          rw [Finset.mem_singleton.mp hi]
          exact hchild r hr u hu, by
          rw [Finset.singleton_biUnion]
          exact hsub, by simp⟩)
    omega
  · push_neg at hA
    by_cases hE : Sup D V' m = ∅
    · have hfin := cnt_replace D R V V' m k 0 hne h Q' hQ' (fun _ => ∅) (fun _ => 0) (by simp)
        (fun r hr => ⟨fun i hi => absurd hi (Finset.notMem_empty i), by
            rw [hE]
            exact Finset.empty_subset _, by simp⟩)
      omega
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hE
      obtain ⟨u, hu, hxu⟩ := (hsupm x).mp hx
      obtain ⟨x', hx', hx'u⟩ := Finset.not_subset.mp (hA u hu)
      have hxx : x ≠ x' := fun e' => hx'u (e' ▸ hxu)
      have huniq : ∀ r r', m ∈ Q' r → m ∈ Q' r' → r = r' := by
        intro r r' hr hr'
        by_contra hrr
        exact hxx (hR r r' hrr x x' (good_sub D V' _ m (hQ' r m hr) hx)
          (good_sub D V' _ m (hQ' r' m hr') hx) (good_sub D V' _ m (hQ' r m hr) hx')
          (good_sub D V' _ m (hQ' r' m hr') hx'))
      have he : ∑ r, (if m ∈ Q' r then 1 else 0 : ℕ) ≤ 1 := by
        rw [← Finset.card_filter]
        exact Finset.card_le_one.mpr (fun a ha b hb =>
          huniq a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)
      have hfin := cnt_replace D R V V' m k 1 hne h Q' hQ' (fun _ => T)
        (fun r => if m ∈ Q' r then 1 else 0) he
        (fun r hr => ⟨fun i hi => hchild r hr i hi, fun v hv => by
            obtain ⟨u', hu', hvu'⟩ := (hsupm v).mp hv
            exact Finset.mem_biUnion.mpr ⟨u', hu', hvu'⟩, by
            rw [if_pos hr]
            omega⟩)
      omega

lemma mono_or {n : ℕ} (V V' : ℕ → (Fin n → Bool) → Bool) (m : ℕ) (T : Finset ℕ)
    (hne : ∀ i, i ≠ m → V' i = V i)
    (hm : ∀ x, V' m x = true ↔ ∃ u ∈ T, V u x = true) (h : MonoV V) : MonoV V' := by
  intro i x y hxy hv
  by_cases hi : i = m
  · rw [hi] at hv ⊢
    obtain ⟨u, hu, huv⟩ := (hm x).mp hv
    exact (hm y).mpr ⟨u, hu, h u x y hxy huv⟩
  · rw [hne i hi] at hv ⊢
    exact h i x y hxy hv

lemma mono_and {n : ℕ} (V V' : ℕ → (Fin n → Bool) → Bool) (m : ℕ) (T : Finset ℕ)
    (hne : ∀ i, i ≠ m → V' i = V i)
    (hm : ∀ x, V' m x = true ↔ ∀ u ∈ T, V u x = true) (h : MonoV V) : MonoV V' := by
  intro i x y hxy hv
  by_cases hi : i = m
  · rw [hi] at hv ⊢
    exact (hm y).mpr (fun u hu => h u x y hxy ((hm x).mp hv u hu))
  · rw [hne i hi] at hv ⊢
    exact h i x y hxy hv

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (W : (Fin n → Bool) → List Bool) : ℕ → (Fin n → Bool) → Bool :=
  fun i x => (W x).getD i false

def wv (n : ℕ) (C : Circuit) : ℕ → (Fin n → Bool) → Bool :=
  val (fun x : Fin n → Bool => C.gates.foldl step (List.ofFn x))

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

lemma val_step {n : ℕ} (W : (Fin n → Bool) → List Bool) (m : ℕ)
    (hlen : ∀ x, (W x).length = m) (g : Gate) :
    val (fun x => step (W x) g) = fun i x =>
      if i = m then g.op.eval (g.inputs.map fun u => val W u x) else val W i x := by
  funext i x
  show (step (W x) g).getD i false = _
  unfold step
  rcases lt_trichotomy i m with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by rw [hlen x]; exact hi), if_neg hi.ne]
    rfl
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen x]; omega), hlen x, if_pos hi, hi]
    simp [val]
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen x]; omega), hlen x, if_neg hi.ne']
    obtain ⟨k, hk⟩ : ∃ k, i - m = k + 1 := ⟨i - m - 1, by omega⟩
    rw [hk]
    show false = (W x).getD i false
    exact (List.getD_eq_default _ _ (by rw [hlen x]; omega)).symm

lemma val_init {n : ℕ} (i : ℕ) (x : Fin n → Bool) :
    val (fun x : Fin n → Bool => List.ofFn x) i x = if h : i < n then x ⟨i, h⟩ else false := by
  show (List.ofFn x).getD i false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < n <;> simp [h]

lemma init_mono (n : ℕ) : MonoV (val (fun x : Fin n → Bool => List.ofFn x)) := by
  intro i x y hxy hv
  rw [val_init] at hv ⊢
  by_cases h : i < n
  · rw [dif_pos h] at hv ⊢
    exact hxy _ hv
  · rw [dif_neg h] at hv
    exact Bool.noConfusion hv

lemma init_cnt {n : ℕ} (D : Finset (Fin n)) {ι : Type} [Fintype ι] (R : ι → Finset (Fin n)) :
    Cnt D R (val (fun x : Fin n → Bool => List.ofFn x)) 0 := by
  intro Q _
  rw [Nat.add_zero]
  refine Finset.sum_le_sum (fun r _ => ?_)
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 1 (fun i _ => ?_)) (by rw [Nat.mul_one])
  refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
  have key : ∀ v ∈ Sup D (val (fun x : Fin n → Bool => List.ofFn x)) i, v.val = i := by
    intro v hv
    have hval := (Finset.mem_filter.mp hv).2.2
    rw [val_init] at hval
    by_cases h : i < n
    · rw [dif_pos h] at hval
      have e := of_decide_eq_true hval
      rw [← e]
    · rw [dif_neg h] at hval
      exact Bool.noConfusion hval
  exact Fin.ext ((key a ha).trans (key b hb).symm)

lemma fold_inv {n : ℕ} (D : Finset (Fin n)) {ι : Type} [Fintype ι] (R : ι → Finset (Fin n))
    (hR : ∀ r r', r ≠ r' → ∀ x x', x ∈ R r → x ∈ R r' → x' ∈ R r → x' ∈ R r' → x = x') :
    ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      ∀ (W : (Fin n → Bool) → List Bool) (m k : ℕ), (∀ x, (W x).length = m) →
        MonoV (val W) → Cnt D R (val W) k →
        MonoV (val fun x => gs.foldl step (W x)) ∧
          Cnt D R (val fun x => gs.foldl step (W x)) (k + gs.countP (fun g => isOr g.op)) := by
  intro gs
  induction gs with
  | nil =>
    intro _ W m k _ hM hC
    exact ⟨hM, by simpa using hC⟩
  | cons g gs ih =>
    intro hfan W m k hlen hM hC
    have hg := hfan g List.mem_cons_self
    have hlen' : ∀ x, (step (W x) g).length = m + 1 := fun x => by simp [step, hlen x]
    have hv := val_step W m hlen g
    have hne : ∀ i, i ≠ m → val (fun x => step (W x) g) i = val W i := by
      intro i hi
      rw [hv]
      funext x
      simp [hi]
    have hT : g.inputs.toFinset.card ≤ 2 := (List.toFinset_card_le _).trans hg.2
    rcases hg.1 with hop | hop
    · have hmm : ∀ x, val (fun x => step (W x) g) m x = true ↔
          ∀ u ∈ g.inputs.toFinset, val W u x = true := by
        intro x
        rw [hv]
        simp [hop, GateOp.eval]
      have hM' := mono_and _ _ m _ hne hmm hM
      have hC' := cnt_and D R _ _ m k _ hne hmm hM hC
      have hih := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) _ (m + 1) k hlen'
        hM' hC'
      have e : k + (g :: gs).countP (fun g => isOr g.op) =
          k + gs.countP (fun g => isOr g.op) := by
        simp [List.countP_cons, hop, isOr]
      rw [e]
      exact hih
    · have hmm : ∀ x, val (fun x => step (W x) g) m x = true ↔
          ∃ u ∈ g.inputs.toFinset, val W u x = true := by
        intro x
        rw [hv]
        simp [hop, GateOp.eval]
      have hM' := mono_or _ _ m _ hne hmm hM
      have hC' := cnt_or D R hR _ _ m k _ hT hne hmm hC
      have hih := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) _ (m + 1) (k + 1)
        hlen' hM' hC'
      have e : k + (g :: gs).countP (fun g => isOr g.op) =
          k + 1 + gs.countP (fun g => isOr g.op) := by
        simp [List.countP_cons, hop, isOr]
        omega
      rw [e]
      exact hih

lemma fold_pre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by simp [step]; omega)]
    unfold step
    exact List.getD_append _ _ _ _ hi

lemma wires_sem : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate), gs[j]? = some g →
    (∀ i ∈ g.inputs, i < w.length + j) →
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false) := by
  intro gs
  induction gs with
  | nil =>
    intro w j g h
    simp at h
  | cons g0 gs ih =>
    intro w j g h hin
    cases j with
    | zero =>
      have hg : g0 = g := by simpa using h
      rw [← hg] at hin ⊢
      rw [List.foldl_cons, Nat.add_zero, fold_pre gs (step w g0) w.length (by simp [step])]
      have e1 : (step w g0).getD w.length false =
          g0.op.eval (g0.inputs.map fun i => w.getD i false) := by
        unfold step
        rw [List.getD_append_right _ _ _ _ (le_refl _)]
        simp
      rw [e1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' := hin i hi
      rw [fold_pre gs (step w g0) i (by simp [step]; omega)]
      unfold step
      exact (List.getD_append _ _ _ _ (by omega)).symm
    | succ j =>
      have h' : gs[j]? = some g := by simpa using h
      have hih := ih (step w g0) j g h' (fun i hi => by
        have := hin i hi
        simp [step]
        omega)
      rw [List.foldl_cons]
      have e : w.length + (j + 1) = (step w g0).length + j := by
        simp [step]
        omega
      rw [e]
      exact hih

lemma and_or_count (d : Gate) : ∀ (gs : List Gate) (S : Finset ℕ),
    (∀ j ∈ S, j < gs.length ∧ isAnd (gs.getD j d).op = true) →
    S.card + gs.countP (fun g => isOr g.op) ≤ gs.length := by
  intro gs
  induction gs with
  | nil =>
    intro S hS
    have e : S = ∅ := Finset.eq_empty_of_forall_notMem (fun j hj => by
      have := (hS j hj).1
      simp at this)
    simp [e]
  | cons g gs ih =>
    intro S hS
    have h1 := ih ((S.erase 0).image Nat.pred) (by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hi0, hiS⟩ := Finset.mem_erase.mp hi
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have h := hS _ hiS
      simp only [List.length_cons, List.getD_cons_succ] at h
      exact ⟨by simp; omega, by simpa using h.2⟩)
    have h2 : ((S.erase 0).image Nat.pred).card = (S.erase 0).card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb e
      have ha' := (Finset.mem_erase.mp (Finset.mem_coe.mp ha)).1
      have hb' := (Finset.mem_erase.mp (Finset.mem_coe.mp hb)).1
      simp only [Nat.pred_eq_sub_one] at e
      omega
    by_cases h0 : 0 ∈ S
    · have h3 := Finset.card_erase_of_mem h0
      have h4 : 0 < S.card := Finset.card_pos.mpr ⟨0, h0⟩
      have h5 : isAnd g.op = true := by simpa using (hS 0 h0).2
      have h6 : isOr g.op = false := by
        cases hg : g.op <;> simp [hg, isAnd, isOr] at h5 ⊢
      have h7 : (g :: gs).countP (fun g => isOr g.op) = gs.countP (fun g => isOr g.op) := by
        simp [List.countP_cons, h6]
      rw [h7, List.length_cons]
      omega
    · have h3 : S.erase 0 = S := Finset.erase_eq_of_notMem h0
      rw [h3] at h1 h2
      have h7 : (g :: gs).countP (fun g => isOr g.op) ≤ gs.countP (fun g => isOr g.op) + 1 := by
        rw [List.countP_cons]
        split <;> omega
      rw [List.length_cons]
      omega

lemma kind_bound {n : ℕ} (D : Finset (Fin n)) {ι : Type} [Fintype ι] (R : ι → Finset (Fin n))
    (V : ℕ → (Fin n → Bool) → Bool) (k B : ℕ) (hC : Cnt D R V k) (S : Finset ℕ)
    (Wt : ι → ℕ → ℕ → Prop)
    (h1 : ∀ r a j, Wt r a j → Good D V (R r) a ∧ j ∈ S ∧ a < B)
    (h2 : ∀ r a j r' a', Wt r a j → Wt r' a' j → r = r' ∧ a = a')
    (F : Finset (ι × Fin n)) (hF : ∀ s ∈ F, ∃ a j, Wt s.1 a j ∧ s.2 ∈ Sup D V a) :
    F.card ≤ S.card + k := by
  classical
  have hQ : ∀ r, ∀ i ∈ (Finset.range B).filter (fun a => ∃ j, Wt r a j), Good D V (R r) i := by
    intro r i hi
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
    exact (h1 r i j hj).1
  have c1 := hC (fun r => (Finset.range B).filter (fun a => ∃ j, Wt r a j)) hQ
  have c2 : F.card ≤ ∑ r, (((Finset.range B).filter (fun a => ∃ j, Wt r a j)).biUnion
      (Sup D V)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)]
    refine Finset.sum_le_sum (fun r _ => ?_)
    refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
    · intro s hs
      obtain ⟨hsF, hsr⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hs)
      obtain ⟨a, j, hw, hv⟩ := hF s hsF
      rw [hsr] at hw
      exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (h1 r a j hw).2.2, j, hw⟩, hv⟩)
    · intro s hs s' hs' e
      have a1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).2
      have a2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hs')).2
      exact Prod.ext (a1.trans a2.symm) e
  have c3 : ∑ r, ((Finset.range B).filter (fun a => ∃ j, Wt r a j)).card ≤ S.card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn
      (fun s => Classical.epsilon (fun j => Wt s.1 s.2 j)) ?_ ?_
    · intro s hs
      have hs' := (Finset.mem_sigma.mp (Finset.mem_coe.mp hs)).2
      have hw := Classical.epsilon_spec (Finset.mem_filter.mp hs').2
      exact Finset.mem_coe.mpr (h1 _ _ _ hw).2.1
    · intro s hs s' hs' e
      have w1 := Classical.epsilon_spec
        (Finset.mem_filter.mp (Finset.mem_sigma.mp (Finset.mem_coe.mp hs)).2).2
      have w2 := Classical.epsilon_spec
        (Finset.mem_filter.mp (Finset.mem_sigma.mp (Finset.mem_coe.mp hs')).2).2
      have e' : Classical.epsilon (fun j => Wt s.1 s.2 j) =
          Classical.epsilon (fun j => Wt s'.1 s'.2 j) := e
      rw [e'] at w1
      obtain ⟨e1, e2⟩ := h2 _ _ _ _ _ w1 w2
      exact Sigma.ext e1 (heq_of_eq e2)
  omega

lemma cast_ne_nat (N : ℕ) (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro e
  have h := congrArg Fin.val e
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h
  have := p.isLt
  omega

lemma nat_inj (N : ℕ) (m l : Fin N) (e : Fin.natAdd N m = Fin.natAdd N l) : m = l := by
  have h := congrArg Fin.val e
  simp only [Fin.coe_natAdd] at h
  exact Fin.ext (by omega)

lemma cast_inj (N : ℕ) (m l : Fin N) (e : Fin.castAdd N m = Fin.castAdd N l) : m = l := by
  have h := congrArg Fin.val e
  simp only [Fin.coe_castAdd] at h
  exact Fin.ext h

end PEqualNP.Outside.L_meta_2838

open PEqualNP.Outside.L_meta_2838 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2838 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) ∧ (∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true) ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1)))).getD a false = true ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N e.2)))).getD c false = true}.ncard ≤ 3 * C.size + 2 * N := by
  classical
  intro q N I _ C hq hN hline huniq hmono hRB hacc hsound
  have hmono' : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    refine ⟨?_, (hmono g hg).2⟩
    rcases (hmono g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  let Dp : Finset (Fin (N + N)) := Finset.univ.filter (fun k => k.val < N)
  let Dl : Finset (Fin (N + N)) := Finset.univ.filter (fun k => N ≤ k.val)
  let Rp : Fin N → Finset (Fin (N + N)) := fun l =>
    Finset.univ.filter (fun k => ∃ p, k = Fin.castAdd N p ∧ I p l)
  let Rl : Fin N → Finset (Fin (N + N)) := fun p =>
    Finset.univ.filter (fun k => ∃ l, k = Fin.natAdd N l ∧ I p l)
  have hRp : ∀ r r', r ≠ r' → ∀ x x', x ∈ Rp r → x ∈ Rp r' → x' ∈ Rp r → x' ∈ Rp r' →
      x = x' := by
    intro l l' hll x x' h1 h2 h3 h4
    obtain ⟨p1, e1, i1⟩ := (Finset.mem_filter.mp h1).2
    obtain ⟨p2, e2, i2⟩ := (Finset.mem_filter.mp h2).2
    obtain ⟨p3, e3, i3⟩ := (Finset.mem_filter.mp h3).2
    obtain ⟨p4, e4, i4⟩ := (Finset.mem_filter.mp h4).2
    have e12 : p2 = p1 := cast_inj N p2 p1 (e2.symm.trans e1)
    have e34 : p4 = p3 := cast_inj N p4 p3 (e4.symm.trans e3)
    rw [e12] at i2
    rw [e34] at i4
    by_contra hx
    have hp : p1 ≠ p3 := fun e => hx (by rw [e1, e3, e])
    exact hll ((huniq p1 p3 hp).unique ⟨i1, i3⟩ ⟨i2, i4⟩)
  have hRl : ∀ r r', r ≠ r' → ∀ x x', x ∈ Rl r → x ∈ Rl r' → x' ∈ Rl r → x' ∈ Rl r' →
      x = x' := by
    intro p p' hpp x x' h1 h2 h3 h4
    obtain ⟨l1, e1, i1⟩ := (Finset.mem_filter.mp h1).2
    obtain ⟨l2, e2, i2⟩ := (Finset.mem_filter.mp h2).2
    obtain ⟨l3, e3, i3⟩ := (Finset.mem_filter.mp h3).2
    obtain ⟨l4, e4, i4⟩ := (Finset.mem_filter.mp h4).2
    have e12 : l2 = l1 := nat_inj N l2 l1 (e2.symm.trans e1)
    have e34 : l4 = l3 := nat_inj N l4 l3 (e4.symm.trans e3)
    rw [e12] at i2
    rw [e34] at i4
    have e := (huniq p p' hpp).unique ⟨i1, i2⟩ ⟨i3, i4⟩
    rw [e1, e3, e]
  have hfp : MonoV (wv (N + N) C) ∧
      Cnt Dp Rp (wv (N + N) C) (0 + C.gates.countP (fun g => isOr g.op)) :=
    fold_inv Dp Rp hRp C.gates hmono' _ (N + N) 0 (fun x => List.length_ofFn) (init_mono _)
      (init_cnt _ _)
  have hfl : MonoV (wv (N + N) C) ∧
      Cnt Dl Rl (wv (N + N) C) (0 + C.gates.countP (fun g => isOr g.op)) :=
    fold_inv Dl Rl hRl C.gates hmono' _ (N + N) 0 (fun x => List.length_ofFn) (init_mono _)
      (init_cnt _ _)
  obtain ⟨hM, hCp⟩ := hfp
  have hCl := hfl.2
  have hget : ∀ j, j < C.gates.length → C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
    intro j hj
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hsemV : ∀ j, j < C.gates.length → ∀ x, wv (N + N) C (N + N + j) x =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map fun i => wv (N + N) C i x) := by
    intro j hj x
    have h := wires_sem C.gates (List.ofFn x) j _ (hget j hj) (fun i hi => by
      rw [List.length_ofFn]
      exact hRB j hj i hi)
    rw [List.length_ofFn] at h
    exact h
  have hgate : ∀ j a c, j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and →
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) →
      ∀ x, wv (N + N) C a x = true → wv (N + N) C c x = true →
        wv (N + N) C (N + N + j) x = true := by
    intro j a c hj hop hin x ha hc
    rw [hsemV j hj x, hop]
    rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, ha, hc]
  have hlt : ∀ j a c, j < C.gates.length →
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) →
      a < N + N + C.gates.length ∧ c < N + N + C.gates.length := by
    intro j a c hj hin
    have h1 := hRB j hj a (by rcases hin with h | h <;> rw [h] <;> simp)
    have h2 := hRB j hj c (by rcases hin with h | h <;> rw [h] <;> simp)
    omega
  let Wit : ℕ → ℕ → ℕ → Prop := fun j a c => j < C.gates.length ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) ∧
    ∀ z : Fin (N + N) → Bool, wv (N + N) C (N + N + j) z = true →
      ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true
  have hinc : ∀ j a c, Wit j a c → ∀ x, wv (N + N) C a x = true → wv (N + N) C c x = true →
      ∃ p0 l0 : Fin N, I p0 l0 ∧ x (Fin.castAdd N p0) = true ∧ x (Fin.natAdd N l0) = true :=
    fun j a c h x ha hc => h.2.2.2 x (hgate j a c h.1 h.2.1 h.2.2.1 x ha hc)
  have hswap : ∀ j a c a' c', Wit j a c → Wit j a' c' →
      (a = a' ∧ c = c') ∨ (a = c' ∧ c = a') := by
    intro j a c a' c' h h'
    have e := h.2.2.1
    have e' := h'.2.2.1
    rcases e with e | e <;> rcases e' with e' | e' <;> rw [e] at e' <;>
      simp only [List.cons.injEq, and_true] at e' <;> tauto
  let S : Finset ℕ := (Finset.range C.gates.length).filter
    (fun j => isAnd (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = true)
  have hS : S.card + C.gates.countP (fun g => isOr g.op) ≤ C.gates.length :=
    and_or_count ⟨GateOp.or, []⟩ C.gates S (fun j hj =>
      ⟨Finset.mem_range.mp (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩)
  let W1 : Fin N → ℕ → ℕ → Prop := fun l a j => ∃ c, Wit j a c ∧
    (∃ p : Fin N, wv (N + N) C a (fun k => decide (k = Fin.castAdd N p)) = true) ∧
    wv (N + N) C c (fun k => decide (k = Fin.natAdd N l)) = true ∧
    ∀ l' : Fin N, wv (N + N) C c (fun k => decide (k = Fin.natAdd N l')) = true → l' = l
  let W2 : Fin N → ℕ → ℕ → Prop := fun p c j => ∃ a, Wit j a c ∧
    (∃ l : Fin N, wv (N + N) C c (fun k => decide (k = Fin.natAdd N l)) = true) ∧
    wv (N + N) C a (fun k => decide (k = Fin.castAdd N p)) = true ∧
    ∀ p' : Fin N, wv (N + N) C a (fun k => decide (k = Fin.castAdd N p')) = true → p' = p
  let F1 : Finset (Fin N × Fin (N + N)) := Finset.univ.filter
    (fun s => ∃ a j, W1 s.1 a j ∧ s.2 ∈ Sup Dp (wv (N + N) C) a)
  let F2 : Finset (Fin N × Fin (N + N)) := Finset.univ.filter
    (fun s => ∃ c j, W2 s.1 c j ∧ s.2 ∈ Sup Dl (wv (N + N) C) c)
  have hK1 : F1.card ≤ S.card + (0 + C.gates.countP (fun g => isOr g.op)) := by
    refine kind_bound Dp Rp (wv (N + N) C) _ (N + N + C.gates.length) hCp S W1 ?_ ?_ F1
      (fun s hs => (Finset.mem_filter.mp hs).2)
    · intro l a j hw
      obtain ⟨c, hW, ⟨p, hap⟩, hcl, hun⟩ := hw
      refine ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hW.1, by rw [hW.2.1]; rfl⟩,
        (hlt j a c hW.1 hW.2.2.1).1⟩
      intro x hx hax
      obtain ⟨p0, l0, hI0, hp0, hl0⟩ := hinc j a c hW
        (fun k => x k || decide (k = Fin.natAdd N l))
        (hM a x _ (fun v hv => by simp [hv]) hax)
        (hM c _ _ (fun v hv => by simp [of_decide_eq_true hv]) hcl)
      have hx0 : x (Fin.castAdd N p0) = true := by
        rcases (Bool.or_eq_true _ _).mp hp0 with h | h
        · exact h
        · exact absurd (of_decide_eq_true h) (cast_ne_nat N p0 l)
      have hl : l0 = l := by
        rcases (Bool.or_eq_true _ _).mp hl0 with h | h
        · exact absurd (Finset.mem_filter.mp (hx _ h)).2 (by simp)
        · exact nat_inj N l0 l (of_decide_eq_true h)
      rw [hl] at hI0
      exact ⟨Fin.castAdd N p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p0, rfl, hI0⟩, hx0⟩
    · intro l a j l' a' hw hw'
      obtain ⟨c, hW, ⟨p, hap⟩, hcl, hun⟩ := hw
      obtain ⟨c', hW', ⟨p', hap'⟩, hcl', hun'⟩ := hw'
      rcases hswap j a c a' c' hW hW' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e2] at hcl'
        exact ⟨(hun l' hcl').symm, e1⟩
      · exfalso
        rw [← e2] at hap'
        obtain ⟨p0, l0, _, _, hl0⟩ := hinc j a c hW
          (fun k => decide (k = Fin.castAdd N p) || decide (k = Fin.castAdd N p'))
          (hM a _ _ (fun v hv => by simp [of_decide_eq_true hv]) hap)
          (hM c _ _ (fun v hv => by simp [of_decide_eq_true hv]) hap')
        rcases (Bool.or_eq_true _ _).mp hl0 with h | h
        · exact cast_ne_nat N p l0 (of_decide_eq_true h).symm
        · exact cast_ne_nat N p' l0 (of_decide_eq_true h).symm
  have hK2 : F2.card ≤ S.card + (0 + C.gates.countP (fun g => isOr g.op)) := by
    refine kind_bound Dl Rl (wv (N + N) C) _ (N + N + C.gates.length) hCl S W2 ?_ ?_ F2
      (fun s hs => (Finset.mem_filter.mp hs).2)
    · intro p c j hw
      obtain ⟨a, hW, ⟨l, hcl⟩, hap, hun⟩ := hw
      refine ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hW.1, by rw [hW.2.1]; rfl⟩,
        (hlt j a c hW.1 hW.2.2.1).2⟩
      intro x hx hcx
      obtain ⟨p0, l0, hI0, hp0, hl0⟩ := hinc j a c hW
        (fun k => x k || decide (k = Fin.castAdd N p))
        (hM a _ _ (fun v hv => by simp [of_decide_eq_true hv]) hap)
        (hM c x _ (fun v hv => by simp [hv]) hcx)
      have hx0 : x (Fin.natAdd N l0) = true := by
        rcases (Bool.or_eq_true _ _).mp hl0 with h | h
        · exact h
        · exact absurd (of_decide_eq_true h).symm (cast_ne_nat N p l0)
      have hp : p0 = p := by
        rcases (Bool.or_eq_true _ _).mp hp0 with h | h
        · exact absurd (Finset.mem_filter.mp (hx _ h)).2 (by simp)
        · exact cast_inj N p0 p (of_decide_eq_true h)
      rw [hp] at hI0
      exact ⟨Fin.natAdd N l0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l0, rfl, hI0⟩, hx0⟩
    · intro p c j p' c' hw hw'
      obtain ⟨a, hW, ⟨l, hcl⟩, hap, hun⟩ := hw
      obtain ⟨a', hW', ⟨l', hcl'⟩, hap', hun'⟩ := hw'
      rcases hswap j a c a' c' hW hW' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1] at hap'
        exact ⟨(hun p' hap').symm, e2⟩
      · exfalso
        rw [← e1] at hcl'
        obtain ⟨p0, l0, _, hp0, _⟩ := hinc j a c hW
          (fun k => decide (k = Fin.natAdd N l') || decide (k = Fin.natAdd N l))
          (hM a _ _ (fun v hv => by simp [of_decide_eq_true hv]) hcl')
          (hM c _ _ (fun v hv => by simp [of_decide_eq_true hv]) hcl)
        rcases (Bool.or_eq_true _ _).mp hp0 with h | h
        · exact cast_ne_nat N p0 l' (of_decide_eq_true h)
        · exact cast_ne_nat N p0 l (of_decide_eq_true h)
  let G1 : Finset (Fin N × Fin N) := Finset.univ.filter
    (fun e => ((e.2, Fin.castAdd N e.1) : Fin N × Fin (N + N)) ∈ F1)
  let G2 : Finset (Fin N × Fin N) := Finset.univ.filter
    (fun e => ((e.1, Fin.natAdd N e.2) : Fin N × Fin (N + N)) ∈ F2)
  have hG1 : G1.card ≤ F1.card :=
    Finset.card_le_card_of_injOn (fun e => ((e.2, Fin.castAdd N e.1) : Fin N × Fin (N + N)))
      (fun e he => (Finset.mem_filter.mp he).2) (fun e _ e' _ h => by
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        exact Prod.ext (cast_inj N _ _ h2) h1)
  have hG2 : G2.card ≤ F2.card :=
    Finset.card_le_card_of_injOn (fun e => ((e.1, Fin.natAdd N e.2) : Fin N × Fin (N + N)))
      (fun e he => (Finset.mem_filter.mp he).2) (fun e _ e' _ h => by
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        exact Prod.ext h1 (nat_inj N _ _ h2))
  refine le_trans (Set.ncard_le_ncard (t := ((G1 ∪ G2 : Finset (Fin N × Fin N)) :
    Set (Fin N × Fin N))) ?_ (Finset.finite_toSet _)) ?_
  · intro e he
    obtain ⟨p, l⟩ := e
    obtain ⟨hI, j, hj, a, c, hop, hin, hsubj, ha, hc⟩ := he
    have hW : Wit j a c := ⟨hj, hop, hin, hsubj⟩
    have ha' : wv (N + N) C a (fun k => decide (k = Fin.castAdd N p)) = true := ha
    have hc' : wv (N + N) C c (fun k => decide (k = Fin.natAdd N l)) = true := hc
    have hpair : ∀ p' l' : Fin N,
        wv (N + N) C a (fun k => decide (k = Fin.castAdd N p')) = true →
        wv (N + N) C c (fun k => decide (k = Fin.natAdd N l')) = true → I p' l' := by
      intro p' l' h1 h2
      obtain ⟨p0, l0, hI0, hp0, hl0⟩ := hinc j a c hW
        (fun k => decide (k = Fin.castAdd N p' ∨ k = Fin.natAdd N l'))
        (hM a _ _ (fun v hv => by simp [of_decide_eq_true hv]) h1)
        (hM c _ _ (fun v hv => by simp [of_decide_eq_true hv]) h2)
      have e1 : p0 = p' := by
        rcases of_decide_eq_true hp0 with h | h
        · exact cast_inj N _ _ h
        · exact absurd h (cast_ne_nat N p0 l')
      have e2 : l0 = l' := by
        rcases of_decide_eq_true hl0 with h | h
        · exact absurd h.symm (cast_ne_nat N p' l0)
        · exact nat_inj N _ _ h
      rw [e1, e2] at hI0
      exact hI0
    by_cases hB : ∀ l' : Fin N,
        wv (N + N) C c (fun k => decide (k = Fin.natAdd N l')) = true → l' = l
    · refine Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, j,
          ⟨c, hW, ⟨p, ha'⟩, hc', hB⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩, ha'⟩⟩⟩))
    · push_neg at hB
      obtain ⟨l', hl', hne⟩ := hB
      have hA : ∀ p' : Fin N,
          wv (N + N) C a (fun k => decide (k = Fin.castAdd N p')) = true → p' = p := by
        intro p' hp'
        by_contra hpp
        exact hne ((huniq p' p hpp).unique ⟨hpair p' l' hp' hl', hpair p l' ha' hl'⟩
          ⟨hpair p' l hp' hc', hpair p l ha' hc'⟩)
      refine Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, j,
          ⟨a, hW, ⟨l, hc'⟩, ha', hA⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩, hc'⟩⟩⟩))
  · rw [Set.ncard_coe_finset]
    have h2 := Finset.card_union_le G1 G2
    have hsz : C.size = C.gates.length := rfl
    omega
