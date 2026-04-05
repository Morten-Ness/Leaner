import Mathlib

open scoped Nat

variable {R S : Type*}

variable [Semiring R] [Semiring S]

theorem sumIDeriv_eq_self_add (p : R[X]) : Polynomial.sumIDeriv p = p + derivative (Polynomial.sumIDeriv p) := by
  rw [Polynomial.sumIDeriv_apply, derivative_sum, sum_range_succ', sum_range_succ,
    add_comm, ← add_zero (Finset.sum _ _)]
  simp_rw [← Function.iterate_succ_apply' derivative, Nat.succ_eq_add_one,
    Function.iterate_zero_apply, iterate_derivative_eq_zero (Nat.lt_succ_self _)]

