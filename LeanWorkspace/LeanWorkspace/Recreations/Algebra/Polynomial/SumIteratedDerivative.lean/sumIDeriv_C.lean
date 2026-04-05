import Mathlib

open scoped Nat

variable {R S : Type*}

variable [Semiring R] [Semiring S]

theorem sumIDeriv_C (a : R) : Polynomial.sumIDeriv (C a) = C a := by
  rw [Polynomial.sumIDeriv_apply, natDegree_C, zero_add, sum_range_one, Function.iterate_zero_apply]

