import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem divMonomial_monomial (a : σ →₀ ℕ) : monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = (1 : MvPolynomial σ R) := AddMonoidAlgebra.of'_divOf _

