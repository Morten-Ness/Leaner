import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem mul_monomial_modMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x * monomial s 1 %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 := x.mul_of'_modOf _

