import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem divMonomial_monomial_mul (a : σ →₀ ℕ) (x : MvPolynomial σ R) :
    monomial a 1 * x /ᵐᵒⁿᵒᵐⁱᵃˡ a = x := x.of'_mul_divOf _

