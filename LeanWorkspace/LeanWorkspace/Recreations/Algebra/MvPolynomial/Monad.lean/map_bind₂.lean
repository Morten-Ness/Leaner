import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem map_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* T) (φ : MvPolynomial σ R) :
    map g (MvPolynomial.bind₂ f φ) = MvPolynomial.bind₂ ((map g).comp f) φ := by
  simp only [MvPolynomial.bind₂, eval₂_comp_right, coe_eval₂Hom, eval₂_map]
  congr 1 with : 1
  simp only [Function.comp_apply, map_X]

