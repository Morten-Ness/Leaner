import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

variable [IsScalarTower R S S]

variable [SMulCommClass R S S]

theorem smeval_pow : ∀ (n : ℕ), (p ^ n).smeval x = (p.smeval x) ^ n
  | 0 => by
    simp only [npow_zero, Polynomial.smeval_one, one_smul]
  | n + 1 => by
    rw [npow_add, Polynomial.smeval_mul, smeval_pow n, pow_one, npow_add, npow_one]
