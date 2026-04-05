import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

variable [SMulCommClass R S S]

theorem smeval_X_pow_mul : ∀ (n : ℕ), (X ^ n * p).smeval x = x ^ n * p.smeval x
  | 0 => by
    simp [npow_zero, one_mul]
  | n + 1 => by
    rw [add_comm, npow_add, mul_assoc, npow_one, Polynomial.smeval_X_mul, smeval_X_pow_mul n, npow_add,
      Polynomial.smeval_X_pow_assoc, npow_one]
