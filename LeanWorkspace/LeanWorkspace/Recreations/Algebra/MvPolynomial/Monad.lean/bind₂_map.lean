import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₂_map (f : S →+* MvPolynomial σ T) (g : R →+* S) (φ : MvPolynomial σ R) :
    MvPolynomial.bind₂ f (map g φ) = MvPolynomial.bind₂ (f.comp g) φ := by simp [MvPolynomial.bind₂]

