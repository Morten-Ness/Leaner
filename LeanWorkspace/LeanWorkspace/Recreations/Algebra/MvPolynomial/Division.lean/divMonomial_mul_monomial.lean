import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem divMonomial_mul_monomial (a : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x * monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = x := x.mul_of'_divOf _

