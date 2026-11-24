import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2772

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def dg : Gate := ⟨GateOp.or, []⟩

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, List.length_append, ih, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega

theorem W_input (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len]; omega), ih]

theorem W_gate (x : List Bool) (gs : List Gate) : ∀ j, j < gs.length →
    (∀ i ∈ (gs.getD j dg).inputs, i < x.length + j) →
    (W gs x).getD (x.length + j) false =
      (gs.getD j dg).op.eval ((gs.getD j dg).inputs.map fun i => (W gs x).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj hin
    rw [List.length_append] at hj
    simp only [List.length_cons, List.length_nil] at hj
    rw [W_snoc]
    rcases Nat.lt_or_ge j gs.length with hlt | hge
    · have e : (gs ++ [g]).getD j dg = gs.getD j dg := List.getD_append _ _ _ _ hlt
      rw [e] at hin ⊢
      rw [List.getD_append _ _ _ _ (by rw [W_len]; omega), ih j hlt hin]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (List.getD_append _ _ _ _ (by rw [W_len]; have := hin i hi; omega)).symm
    · have hj' : j = gs.length := by omega
      subst hj'
      have e : (gs ++ [g]).getD gs.length dg = g := by simp
      rw [e] at hin ⊢
      rw [List.getD_append_right _ _ _ _ (by rw [W_len]), W_len]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (List.getD_append _ _ _ _ (by rw [W_len]; have := hin i hi; omega)).symm

theorem ev2 (R : Bool → Bool → Prop)
    (hand : ∀ a b c d, R a b → R c d → R (a && c) (b && d))
    (hor : ∀ a b c d, R a b → R c d → R (a || c) (b || d))
    (op : GateOp) (ho : op = GateOp.and ∨ op = GateOp.or) (a b c d : Bool)
    (h1 : R a b) (h2 : R c d) : R (op.eval [a, c]) (op.eval [b, d]) := by
  rcases ho with rfl | rfl
  · simpa [GateOp.eval] using hand _ _ _ _ h1 h2
  · simpa [GateOp.eval] using hor _ _ _ _ h1 h2

theorem sim (R : Bool → Bool → Prop) (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hand : ∀ a b c d, R a b → R c d → R (a && c) (b && d))
    (hor : ∀ a b c d, R a b → R c d → R (a || c) (b || d))
    (gs : List Gate) (g b w' : ℕ) (X : List Bool)
    (hop : ∀ j, j < gs.length → (gs.getD j dg).op = GateOp.and ∨ (gs.getD j dg).op = GateOp.or)
    (hlen : ∀ j, j < gs.length → (gs.getD j dg).inputs.length = 2)
    (hrb : ∀ j, j < gs.length → ∀ i ∈ (gs.getD j dg).inputs, i < X.length + j)
    (hg : g < gs.length) (hb : b < 2) (hw' : w' < X.length + g)
    (hR : R ((W gs X).getD ((gs.getD g dg).inputs.getD b 0) false) ((W gs X).getD w' false)) :
    ∀ i, R ((W gs X).getD i false)
      ((W (gs.set g ⟨(gs.getD g dg).op, (gs.getD g dg).inputs.set b w'⟩) X).getD i false) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  rcases Nat.lt_or_ge i X.length with h1 | h1
  · rw [W_input _ _ _ h1, W_input _ _ _ h1]; exact hrefl _
  rcases Nat.lt_or_ge i (X.length + gs.length) with h2 | h2
  swap
  · rw [List.getD_eq_default _ _ (by rw [W_len]; exact h2),
      List.getD_eq_default _ _ (by rw [W_len, List.length_set]; exact h2)]
    exact hrefl _
  obtain ⟨j, rfl⟩ : ∃ j, i = X.length + j := ⟨i - X.length, by omega⟩
  have hj : j < gs.length := by omega
  have hl := hlen j hj
  have hr := hrb j hj
  have ho := hop j hj
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hl
  have hp : p < X.length + j := hr p (by rw [hpq]; simp)
  have hq : q < X.length + j := hr q (by rw [hpq]; simp)
  rw [W_gate X gs j hj hr]
  by_cases hjg : j = g
  · subst hjg
    have e : (gs.set j ⟨(gs.getD j dg).op, (gs.getD j dg).inputs.set b w'⟩).getD j dg
        = ⟨(gs.getD j dg).op, (gs.getD j dg).inputs.set b w'⟩ := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [W_gate X _ j (by rw [List.length_set]; exact hj) (by
      rw [e]; intro i hi
      rcases List.mem_or_eq_of_mem_set hi with h | h
      · exact hr i h
      · omega)]
    rw [e]
    simp only []
    generalize W (gs.set j ⟨(gs.getD j dg).op, (gs.getD j dg).inputs.set b w'⟩) X = B at ih ⊢
    rw [hpq] at hR ⊢
    have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl
    · simp only [List.set_cons_zero, List.map_cons, List.map_nil]
      have hR' : R ((W gs X).getD p false) ((W gs X).getD w' false) := by simpa using hR
      exact ev2 R hand hor _ ho _ _ _ _ (htrans _ _ _ hR' (ih w' hw')) (ih q hq)
    · simp only [List.set_cons_succ, List.set_cons_zero, List.map_cons, List.map_nil]
      have hR' : R ((W gs X).getD q false) ((W gs X).getD w' false) := by simpa using hR
      exact ev2 R hand hor _ ho _ _ _ _ (ih p hp) (htrans _ _ _ hR' (ih w' hw'))
  · have e : (gs.set g ⟨(gs.getD g dg).op, (gs.getD g dg).inputs.set b w'⟩).getD j dg
        = gs.getD j dg := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (fun h => hjg h.symm),
        ← List.getD_eq_getElem?_getD]
    rw [W_gate X _ j (by rw [List.length_set]; exact hj) (by rw [e]; exact hr)]
    rw [e, hpq]
    simp only [List.map_cons, List.map_nil]
    exact ev2 R hand hor _ ho _ _ _ _ (ih p hp) (ih q hq)

theorem getD_mem (gs : List Gate) (j : ℕ) (hj : j < gs.length) : gs.getD j dg ∈ gs := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

end PEqualNP.Outside.L_meta_2772

theorem PEqualNP.Outside.L_meta_2772 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
    PEqualNP.MetaComplexity.circuitFun n C x = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧
  PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ∧
  (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  intro n C g b w w' ⟨hAO, hRB, hg, hb, hw, hw', h1, h2⟩
  obtain ⟨hao, hrb, hl2⟩ := hAO
  subst hw
  have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C g ∈ C.gates :=
    PEqualNP.Outside.L_meta_2772.getD_mem C.gates g hg
  have hop : ∀ j, j < C.gates.length →
      (C.gates.getD j PEqualNP.Outside.L_meta_2772.dg).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (C.gates.getD j PEqualNP.Outside.L_meta_2772.dg).op = PEqualNP.CircuitLowerBounds.GateOp.or :=
    fun j hj => hao _ (PEqualNP.Outside.L_meta_2772.getD_mem C.gates j hj)
  have hlen : ∀ j, j < C.gates.length →
      (C.gates.getD j PEqualNP.Outside.L_meta_2772.dg).inputs.length = 2 :=
    fun j hj => hl2 _ (PEqualNP.Outside.L_meta_2772.getD_mem C.gates j hj)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro G hG
    rcases List.mem_or_eq_of_mem_set hG with h | h
    · exact hao G h
    · subst h
      have h3 := hao _ hmem
      exact h3
  · intro j hj i hi
    have hj' : j < C.gates.length := by
      have := hj
      simp only [List.length_set] at this
      exact this
    by_cases hjg : j = g
    · subst hjg
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt (⟨C.gates.set j ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C j).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) j
          = ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C j).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.set b w'⟩ := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj']
      rw [e] at hi
      rcases List.mem_or_eq_of_mem_set hi with h | h
      · exact hrb j hj' i h
      · omega
    · have e : PEqualNP.MetaComplexity.NestedCover.gateAt (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) j
          = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (fun h => hjg h.symm),
          ← List.getD_eq_getElem?_getD]
      rw [e] at hi
      exact hrb j hj' i hi
  · intro G hG
    rcases List.mem_or_eq_of_mem_set hG with h | h
    · exact hl2 G h
    · subst h
      show ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w').length = 2
      rw [List.length_set]
      exact hl2 _ hmem
  · funext x
    have hXl : (List.ofFn x).length = n := List.length_ofFn
    have hrb' : ∀ j, j < C.gates.length →
        ∀ i ∈ (C.gates.getD j PEqualNP.Outside.L_meta_2772.dg).inputs, i < (List.ofFn x).length + j := by
      intro j hj i hi
      rw [hXl]
      exact hrb j hj i hi
    have hw'' : w' < (List.ofFn x).length + g := by rw [hXl]; exact hw'
    show (PEqualNP.Outside.L_meta_2772.W (C.gates.set g ⟨(C.gates.getD g PEqualNP.Outside.L_meta_2772.dg).op, (C.gates.getD g PEqualNP.Outside.L_meta_2772.dg).inputs.set b w'⟩) (List.ofFn x)).getD C.output false
      = (PEqualNP.Outside.L_meta_2772.W C.gates (List.ofFn x)).getD C.output false
    by_cases hc : (PEqualNP.Outside.L_meta_2772.W C.gates (List.ofFn x)).getD w' false = true
    · have hle := PEqualNP.Outside.L_meta_2772.sim (fun a b => a = true → b = true)
        (fun _ h => h) (fun _ _ _ h h' k => h' (h k))
        (by intro a b c d h1 h2; cases a <;> cases b <;> cases c <;> cases d <;> simp_all)
        (by intro a b c d h1 h2; cases a <;> cases b <;> cases c <;> cases d <;> simp_all)
        C.gates g b w' (List.ofFn x) hop hlen hrb' hg hb hw'' (h1 x)
      have hF : (PEqualNP.Outside.L_meta_2772.W C.gates (List.ofFn x)).getD C.output false = true :=
        h2 x hc
      exact (hle C.output hF).trans hF.symm
    · have hf : (PEqualNP.Outside.L_meta_2772.W C.gates (List.ofFn x)).getD w' false = false := by
        simpa using hc
      have hf2 : (PEqualNP.Outside.L_meta_2772.W C.gates (List.ofFn x)).getD
          ((C.gates.getD g PEqualNP.Outside.L_meta_2772.dg).inputs.getD b 0) false = false := by
        by_contra h
        exact hc (h1 x (Bool.eq_true_of_not_eq_false h))
      have heq := PEqualNP.Outside.L_meta_2772.sim Eq
        (fun _ => rfl) (fun _ _ _ h h' => h.trans h')
        (by intro a b c d h1 h2; rw [h1, h2])
        (by intro a b c d h1 h2; rw [h1, h2])
        C.gates g b w' (List.ofFn x) hop hlen hrb' hg hb hw'' (hf2.trans hf.symm)
      exact (heq C.output).symm
  · show (C.gates.set g _).length = C.gates.length
    exact List.length_set
