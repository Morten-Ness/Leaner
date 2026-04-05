import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [Semiring R]

theorem closure_pow (s : Set R) : ∀ n : ℕ, closure s ^ n = closure (s ^ n)
  | 0 => by rw [pow_zero, pow_zero, AddSubmonoid.one_eq_closure_one_set]
  | n + 1 => by rw [pow_succ, pow_succ, closure_pow s n, AddSubmonoid.closure_mul_closure]
