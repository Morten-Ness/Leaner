import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_monomial (d : σ →₀ ℕ) (r : R) :
    MvPolynomial.expand p (monomial d r) = monomial (p • d) r := by
  rw [MvPolynomial.expand, bind₁_monomial, monomial_eq, Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul]
  · simp

