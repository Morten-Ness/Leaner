import Mathlib

variable {R A B : Type*}

variable [Semiring R] [Semiring A]

variable [Module R A] [IsScalarTower R A A]

theorem pow_mulRight (a : A) (n : ℕ) : mulRight R a ^ n = mulRight R (a ^ n) := match n with
  | 0 => by rw [pow_zero, pow_zero, mulRight_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ', mulRight_mul, Module.End.mul_eq_comp, pow_mulRight]

