import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem monomial_mul_modMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    monomial s 1 * x %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 := x.of'_mul_modOf _

