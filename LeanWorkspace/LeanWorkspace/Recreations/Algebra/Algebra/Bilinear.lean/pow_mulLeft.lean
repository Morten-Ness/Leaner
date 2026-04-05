import Mathlib

variable {R A B : Type*}

variable [Semiring R] [Semiring A]

variable [Module R A] [SMulCommClass R A A]

theorem pow_mulLeft (a : A) (n : ℕ) : mulLeft R a ^ n = mulLeft R (a ^ n) := match n with
  | 0 => by rw [pow_zero, pow_zero, mulLeft_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ, mulLeft_mul, Module.End.mul_eq_comp, pow_mulLeft]

