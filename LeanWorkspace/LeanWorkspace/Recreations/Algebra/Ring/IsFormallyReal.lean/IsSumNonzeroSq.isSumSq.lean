import Mathlib

variable {R : Type*}

theorem IsSumNonzeroSq.isSumSq [AddMonoid R] [Mul R] {s : R}
    (h : IsSumNonzeroSq s) : IsSumSq s := by
  induction h <;> aesop

