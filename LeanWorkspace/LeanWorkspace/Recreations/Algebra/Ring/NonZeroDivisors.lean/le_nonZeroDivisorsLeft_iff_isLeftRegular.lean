import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem le_nonZeroDivisorsLeft_iff_isLeftRegular {S : Submonoid R} :
    S ≤ nonZeroDivisorsLeft R ↔ ∀ s : S, IsLeftRegular (s : R) := by
  simp_rw [SetLike.le_def, isLeftRegular_iff_mem_nonZeroDivisorsLeft, Subtype.forall]

