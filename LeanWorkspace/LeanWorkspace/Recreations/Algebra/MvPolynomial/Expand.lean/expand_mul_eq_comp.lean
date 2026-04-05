import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_mul_eq_comp (q : ℕ) :
    MvPolynomial.expand (σ := σ) (R := R) (p * q) = (MvPolynomial.expand p).comp (MvPolynomial.expand q) := by
  ext1 i
  simp [pow_mul]

