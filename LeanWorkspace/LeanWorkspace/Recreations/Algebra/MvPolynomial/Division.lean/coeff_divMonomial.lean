import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem coeff_divMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) (s' : σ →₀ ℕ) :
    coeff s' (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff (s + s') x := rfl

