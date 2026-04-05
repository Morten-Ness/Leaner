import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem coeff_modMonomial_of_not_le {s' s : σ →₀ ℕ} (x : MvPolynomial σ R) (h : ¬s ≤ s') :
    coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff s' x := x.modOf_apply_of_not_exists_add s s'
    (by
      rintro ⟨d, rfl⟩
      exact h le_self_add)

