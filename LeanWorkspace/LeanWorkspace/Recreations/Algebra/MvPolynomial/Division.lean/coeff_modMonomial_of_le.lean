import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem coeff_modMonomial_of_le {s' s : σ →₀ ℕ} (x : MvPolynomial σ R) (h : s ≤ s') :
    coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = 0 := x.modOf_apply_of_exists_add _ _ <| exists_add_of_le h

