import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3505

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def fix (X Y : Finset ℕ) : Gate → Gate
  | ⟨GateOp.and, [a, b]⟩ => if a ∈ X ∧ b ∈ Y then ⟨GateOp.and, [a, b]⟩ else ⟨GateOp.and, [b, a]⟩
  | g => g

theorem fix_cases (X Y : Finset ℕ) (g : Gate) :
    fix X Y g = g ∨ ∃ a b, g = ⟨GateOp.and, [a, b]⟩ ∧ fix X Y g = ⟨GateOp.and, [b, a]⟩ := by
  rcases g with ⟨op, ins⟩
  rcases op with _ | _ | _ | m | _
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · left; rfl
    · left; rfl
    · by_cases h : a ∈ X ∧ b ∈ Y
      · left; simp [fix, h]
      · right; exact ⟨a, b, rfl, by simp [fix, h]⟩
    · left; rfl
  all_goals (left; rfl)

theorem fix_op (X Y : Finset ℕ) (g : Gate) : (fix X Y g).op = g.op := by
  rcases fix_cases X Y g with h | ⟨a, b, rfl, h⟩
  · rw [h]
  · rw [h]

theorem fix_mem (X Y : Finset ℕ) (g : Gate) (i : ℕ) : i ∈ (fix X Y g).inputs ↔ i ∈ g.inputs := by
  rcases fix_cases X Y g with h | ⟨a, b, rfl, h⟩
  · rw [h]
  · rw [h]; simp [or_comm]

theorem fix_len (X Y : Finset ℕ) (g : Gate) : (fix X Y g).inputs.length = g.inputs.length := by
  rcases fix_cases X Y g with h | ⟨a, b, rfl, h⟩
  · rw [h]
  · rw [h]; simp

theorem fix_or (X Y : Finset ℕ) (g : Gate) (hg : g.op = GateOp.or) : fix X Y g = g := by
  rcases fix_cases X Y g with h | ⟨a, b, rfl, h⟩
  · exact h
  · simp at hg

theorem fix_eval (X Y : Finset ℕ) (g : Gate) (f : ℕ → Bool) :
    (fix X Y g).op.eval ((fix X Y g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  rcases fix_cases X Y g with h | ⟨a, b, rfl, h⟩
  · rw [h]
  · rw [h]; simp [GateOp.eval, Bool.and_comm]

theorem fix_and (X Y : Finset ℕ) (a b : ℕ) (hab : a ∈ X ∧ b ∈ Y ∨ a ∈ Y ∧ b ∈ X) :
    ∃ c d, (fix X Y ⟨GateOp.and, [a, b]⟩).inputs = [c, d] ∧ c ∈ X ∧ d ∈ Y := by
  by_cases h : a ∈ X ∧ b ∈ Y
  · exact ⟨a, b, by simp [fix, h], h.1, h.2⟩
  · have h2 : a ∈ Y ∧ b ∈ X := by tauto
    exact ⟨b, a, by simp [fix, h], h2.2, h2.1⟩

def lift (X Y : Finset ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (fix X Y), C.output⟩

theorem lift_wires (X Y : Finset ℕ) (C : Circuit) (x : List Bool) :
    (lift X Y C).wires x = C.wires x := by
  unfold Circuit.wires lift
  rw [List.foldl_map]
  congr 1
  funext w g
  rw [fix_eval]

theorem lift_gateAt (X Y : Finset ℕ) (C : Circuit) (j : ℕ) :
    gateAt (lift X Y C) j = fix X Y (gateAt C j) := by
  unfold gateAt lift
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.gates[j]? with
  | none => simp [fix]
  | some g => simp

end PEqualNP.Outside.L_meta_3505

open PEqualNP.Outside.L_meta_3505 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_3505 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x3 ∧ x12 ∈ x4 := by
  intro n C X Y hAO hand
  obtain ⟨hAnd, hRB, hLen⟩ := hAO
  refine ⟨lift X Y C, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [lift, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [fix_op]
    exact hAnd g0 hg0
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [lift] using hj
    rw [lift_gateAt, fix_mem] at hi
    exact hRB j hj' i hi
  · intro g hg
    simp only [lift, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [fix_len]
    exact hLen g0 hg0
  · simp [lift, PEqualNP.CircuitLowerBounds.Circuit.size]
  · funext x
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, lift_wires]
    rfl
  · intro j
    rw [lift_gateAt, fix_op]
  · intro j hj
    rw [lift_gateAt, fix_or X Y _ hj]
  · intro j hj hop
    have hj' : j < C.gates.length := by simpa [lift] using hj
    rw [lift_gateAt, fix_op] at hop
    rw [lift_gateAt]
    obtain ⟨a, b, hin, hab⟩ := hand j hj' hop
    have hg : gateAt C j = ⟨GateOp.and, [a, b]⟩ := by
      rcases hgj : gateAt C j with ⟨op, ins⟩
      rw [hgj] at hop hin
      simp only at hop hin
      rw [hop, hin]
    rw [hg]
    exact fix_and X Y a b hab
