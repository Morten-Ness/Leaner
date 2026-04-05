import Mathlib

variable {R : Type*}

theorem IsSumSq.natCast {R : Type*} [NonAssocSemiring R] (n : ℕ) : IsSumSq (n : R) := by
  induction n <;> aesop

