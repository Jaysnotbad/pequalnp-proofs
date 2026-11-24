import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1660

open PEqualNP.CircuitLowerBounds

def wiresL (gates : List Gate) (x : List Bool) : List Bool :=
  gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wiresL_snoc (l : List Gate) (g : Gate) (x : List Bool) :
    wiresL (l ++ [g]) x =
      wiresL l x ++ [g.op.eval (g.inputs.map fun i => (wiresL l x).getD i false)] := by
  simp [wiresL, List.foldl_append]

lemma wiresL_length (l : List Gate) (x : List Bool) :
    (wiresL l x).length = x.length + l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [wiresL]
  | append_singleton l g ih =>
    rw [wiresL_snoc]
    simp [ih]
    omega

lemma getD_snoc_ne (A : List Bool) (v : Bool) (w : ℕ) (h : w ≠ A.length) :
    (A ++ [v]).getD w false = A.getD w false := by
  rcases Nat.lt_or_gt_of_ne h with h1 | h1
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · have h2 : (A ++ [v])[w]? = none := List.getElem?_eq_none (by simp; omega)
    have h3 : A[w]? = none := List.getElem?_eq_none (by omega)
    simp [List.getD_eq_getElem?_getD, h2, h3]

lemma getD_snoc_eq (A : List Bool) (v : Bool) (m : ℕ) (h : m = A.length) :
    (A ++ [v]).getD m false = v := by
  subst h
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_getD (n : ℕ) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    (List.ofFn x).getD w false = x ⟨w, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

lemma ofFn_getD_ge (n : ℕ) (x : Fin n → Bool) (w : ℕ) (h : ¬ w < n) :
    (List.ofFn x).getD w false = false := by
  simp [List.getD_eq_getElem?_getD, h]

lemma key (n : ℕ) (gates : List Gate) : (∀ g ∈ gates, g.inputs.length ≤ 2) → ∀ W : Finset ℕ,
    ∃ D : Finset (Fin n), D.card ≤ W.card + gates.length ∧ ∀ x x' : Fin n → Bool,
      (∀ d ∈ D, x d = x' d) → ∀ w ∈ W,
        (wiresL gates (List.ofFn x)).getD w false =
          (wiresL gates (List.ofFn x')).getD w false := by
  induction gates using List.reverseRecOn with
  | nil =>
    intro _ W
    refine ⟨Finset.univ.filter (fun d : Fin n => (d : ℕ) ∈ W), ?_, ?_⟩
    · have h1 : (Finset.univ.filter (fun d : Fin n => (d : ℕ) ∈ W)).card ≤ W.card :=
        Finset.card_le_card_of_injOn (fun d => (d : ℕ)) (by intro d hd; simpa using hd)
          (by intro a _ b _ h; exact Fin.ext h)
      simpa using h1
    · intro x x' hx w hw
      simp only [wiresL, List.foldl_nil]
      by_cases h : w < n
      · rw [ofFn_getD n x w h, ofFn_getD n x' w h]
        exact hx _ (by simp [hw])
      · rw [ofFn_getD_ge n x w h, ofFn_getD_ge n x' w h]
  | append_singleton l g ih =>
    intro hfan W
    have hfl : ∀ g' ∈ l, g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hg : g.inputs.length ≤ 2 := hfan g (by simp)
    have hlen : ∀ x : Fin n → Bool, (wiresL l (List.ofFn x)).length = n + l.length := by
      intro x
      rw [wiresL_length]
      simp
    by_cases hm : n + l.length ∈ W
    · obtain ⟨D, hc, hD⟩ := ih hfl (W.erase (n + l.length) ∪ g.inputs.toFinset)
      refine ⟨D, ?_, ?_⟩
      · have h1 : (W.erase (n + l.length) ∪ g.inputs.toFinset).card ≤
            (W.erase (n + l.length)).card + g.inputs.toFinset.card := Finset.card_union_le _ _
        have h2 : (W.erase (n + l.length)).card = W.card - 1 := Finset.card_erase_of_mem hm
        have h3 : g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le _
        have h4 : 0 < W.card := Finset.card_pos.mpr ⟨_, hm⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · intro x x' hx w hw
        rw [wiresL_snoc, wiresL_snoc]
        by_cases hw' : w = n + l.length
        · rw [getD_snoc_eq _ _ _ (hw'.trans (hlen x).symm),
            getD_snoc_eq _ _ _ (hw'.trans (hlen x').symm)]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hD x x' hx i (by simp [hi])
        · rw [getD_snoc_ne _ _ _ (by rw [hlen]; exact hw'),
            getD_snoc_ne _ _ _ (by rw [hlen]; exact hw')]
          exact hD x x' hx w (by simp [hw, hw'])
    · obtain ⟨D, hc, hD⟩ := ih hfl W
      refine ⟨D, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro x x' hx w hw
        have hw' : w ≠ n + l.length := fun h => hm (h ▸ hw)
        rw [wiresL_snoc, wiresL_snoc, getD_snoc_ne _ _ _ (by rw [hlen]; exact hw'),
          getD_snoc_ne _ _ _ (by rw [hlen]; exact hw')]
        exact hD x x' hx w hw

lemma split (N : ℕ) (v : Fin (N + N)) :
    (∃ p : Fin N, v = Fin.castAdd N p) ∨ (∃ l : Fin N, v = Fin.natAdd N l) := by
  by_cases h : v.val < N
  · exact Or.inl ⟨⟨v.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨v.val - N, by omega⟩, Fin.ext (by simp; omega)⟩

lemma cast_ne_nat (N : ℕ) (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have h1 := congrArg Fin.val h
  simp at h1
  omega

lemma nat_inj (N : ℕ) (a l : Fin N) : Fin.natAdd N a = Fin.natAdd N l ↔ a = l := by
  constructor
  · intro h
    have h1 := congrArg Fin.val h
    simp at h1
    exact Fin.ext h1
  · intro h
    rw [h]

end PEqualNP.Outside.L_meta_1660

theorem PEqualNP.Outside.L_meta_1660 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1) → (∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z1 = false) → 2 * N ≤ C.size + 1 := by
  intro q N I inst C hq hN hline hpts hmono hrb hacc hsound
  obtain ⟨D, hc, hD⟩ := PEqualNP.Outside.L_meta_1660.key (N + N) C.gates
    (fun g hg => (hmono g hg).2) {C.output}
  have hval : ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z =
      (PEqualNP.Outside.L_meta_1660.wiresL C.gates (List.ofFn z)).getD C.output false :=
    fun z => rfl
  have hflip : ∀ (v : Fin (N + N)) (z z' : Fin (N + N) → Bool), (∀ d, d ≠ v → z d = z' d) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true →
      PEqualNP.MetaComplexity.circuitFun (N + N) C z' = false → v ∈ D := by
    intro v z z' hz h1 h2
    by_contra hv
    have h3 := hD z z' (fun d hd => hz d (fun h => hv (h ▸ hd))) C.output (by simp)
    rw [← hval, ← hval, h1, h2] at h3
    exact Bool.noConfusion h3
  have hN3 : 3 ≤ N := by
    have h0 : 0 ≤ q ^ 2 := Nat.zero_le _
    omega
  have hall : ∀ v : Fin (N + N), v ∈ D := by
    intro v
    rcases PEqualNP.Outside.L_meta_1660.split N v with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · obtain ⟨p', hp'⟩ : ∃ p' : Fin N, p ≠ p' := by
        by_cases h0 : p.val = 0
        · exact ⟨⟨1, by omega⟩, fun h => by have h1 := congrArg Fin.val h; simp at h1; omega⟩
        · exact ⟨⟨0, by omega⟩, fun h => by have h1 := congrArg Fin.val h; simp at h1; omega⟩
      obtain ⟨l, ⟨hl, _⟩, _⟩ := hpts p p' hp'
      refine hflip _ (fun k1 => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l))
        (fun k1 => decide (k1 = Fin.natAdd N l)) ?_ (hacc p l hl) ?_
      · intro d hd
        simp only [hd, false_or]
      · apply hsound
        · have h5 : (Finset.univ.filter (fun l1b : Fin N =>
              (fun k1 => decide (k1 = Fin.natAdd N l)) (Fin.natAdd N l1b) = true)) = {l} := by
            ext a
            simp [PEqualNP.Outside.L_meta_1660.nat_inj]
          rw [h5]
          simp
          omega
        · rintro ⟨p1, l1, _, h1, _⟩
          exact PEqualNP.Outside.L_meta_1660.cast_ne_nat N p1 l (of_decide_eq_true h1)
    · have hne : (Finset.univ.filter (fun p0 => I p0 l)).Nonempty := by
        rw [← Finset.card_pos, hline]
        omega
      obtain ⟨p, hp⟩ := hne
      have hI : I p l := (Finset.mem_filter.mp hp).2
      refine hflip _ (fun k1 => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l))
        (fun k1 => decide (k1 = Fin.castAdd N p)) ?_ (hacc p l hI) ?_
      · intro d hd
        simp only [hd, or_false]
      · apply hsound
        · have h5 : (Finset.univ.filter (fun l1b : Fin N =>
              (fun k1 => decide (k1 = Fin.castAdd N p)) (Fin.natAdd N l1b) = true)) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro a _ h
            exact PEqualNP.Outside.L_meta_1660.cast_ne_nat N p a (of_decide_eq_true h).symm
          rw [h5]
          simp
        · rintro ⟨p1, l1, _, _, h2⟩
          exact PEqualNP.Outside.L_meta_1660.cast_ne_nat N p l1 (of_decide_eq_true h2).symm
  have hDu : D = Finset.univ := Finset.eq_univ_of_forall hall
  have hcard : D.card = N + N := by
    rw [hDu]
    simp
  have hs : C.size = C.gates.length := rfl
  simp only [Finset.card_singleton] at hc
  omega
