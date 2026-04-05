import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_nonneg_iff_pos_imp_nonneg [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    0 ≤ a * b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) := by
  refine mul_nonneg_iff.trans ?_
  simp_rw [← not_le, ← or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

