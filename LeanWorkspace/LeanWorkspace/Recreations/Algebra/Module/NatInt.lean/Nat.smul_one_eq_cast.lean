import Mathlib

variable {R S M M₂ : Type*}

theorem Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring R] (m : ℕ) : m • (1 : R) = ↑m := by
  rw [nsmul_eq_mul, mul_one]

