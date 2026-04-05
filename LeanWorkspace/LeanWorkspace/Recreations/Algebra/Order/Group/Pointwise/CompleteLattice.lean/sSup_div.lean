import Mathlib

open scoped Pointwise

variable {M : Type*}

variable [CompleteLattice M]

variable [Group M] [MulLeftMono M] [MulRightMono M]
  (s t : Set M)

theorem sSup_div : sSup (s / t) = sSup s / sInf t := by simp_rw [div_eq_mul_inv, sSup_mul, sSup_inv]

