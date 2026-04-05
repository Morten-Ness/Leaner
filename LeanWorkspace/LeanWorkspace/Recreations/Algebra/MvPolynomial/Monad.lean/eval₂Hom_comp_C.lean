import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem eval₂Hom_comp_C (f : R →+* S) (g : σ → S) : (eval₂Hom f g).comp C = f := by
  ext1 r
  exact eval₂_C f g r

