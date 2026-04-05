import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem divMonomial_add (a b : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x /ᵐᵒⁿᵒᵐⁱᵃˡ (a + b) = x /ᵐᵒⁿᵒᵐⁱᵃˡ a /ᵐᵒⁿᵒᵐⁱᵃˡ b := x.divOf_add _ _

