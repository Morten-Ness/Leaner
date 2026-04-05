import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem join₂_map (f : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    MvPolynomial.join₂ (map f φ) = MvPolynomial.bind₂ f φ := by simp only [MvPolynomial.join₂, MvPolynomial.bind₂, eval₂Hom_map_hom, RingHom.id_comp]

