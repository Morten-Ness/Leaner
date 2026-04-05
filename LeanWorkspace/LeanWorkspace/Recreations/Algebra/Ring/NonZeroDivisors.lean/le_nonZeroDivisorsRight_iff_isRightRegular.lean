import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem le_nonZeroDivisorsRight_iff_isRightRegular {S : Submonoid R} :
    S ≤ nonZeroDivisorsRight R ↔ ∀ s : S, IsRightRegular (s : R) := by
  simp_rw [SetLike.le_def, isRightRegular_iff_mem_nonZeroDivisorsRight, Subtype.forall]

