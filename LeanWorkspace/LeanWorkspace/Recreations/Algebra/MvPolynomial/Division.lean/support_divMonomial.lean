import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem support_divMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    (x /ᵐᵒⁿᵒᵐⁱᵃˡ s).support = x.support.preimage _ (add_right_injective s).injOn := rfl

