import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

variable [IsScalarTower R S S]

theorem smeval_mul_X_pow : ∀ (n : ℕ), (p * X ^ n).smeval x = p.smeval x * x ^ n
  | 0 => by
    simp only [npow_zero, mul_one]
  | n + 1 => by
    rw [npow_add, ← mul_assoc, npow_one, Polynomial.smeval_mul_X, smeval_mul_X_pow n, npow_add,
      ← Polynomial.smeval_assoc_X_pow, npow_one]
