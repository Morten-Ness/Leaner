import Mathlib

open scoped Nat

variable {R S : Type*}

variable [Semiring R] [Semiring S]

theorem sumIDeriv_X : Polynomial.sumIDeriv X = X + C 1 := by
  rw [Polynomial.sumIDeriv_apply, natDegree_X, sum_range_succ, sum_range_one, Function.iterate_zero_apply,
    Function.iterate_one, derivative_X, eq_natCast, Nat.cast_one]

