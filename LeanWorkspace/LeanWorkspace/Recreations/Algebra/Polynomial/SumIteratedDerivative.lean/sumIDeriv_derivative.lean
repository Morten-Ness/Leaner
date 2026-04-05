import Mathlib

open scoped Nat

variable {R S : Type*}

variable [Semiring R] [Semiring S]

theorem sumIDeriv_derivative (p : R[X]) : Polynomial.sumIDeriv (derivative p) = derivative (Polynomial.sumIDeriv p) := by
  rw [Polynomial.sumIDeriv_apply_of_le ((natDegree_derivative_le p).trans tsub_le_self), Polynomial.sumIDeriv_apply,
    derivative_sum]
  simp_rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

