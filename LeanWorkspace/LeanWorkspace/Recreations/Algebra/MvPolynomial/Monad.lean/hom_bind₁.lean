import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem hom_bind₁ (f : MvPolynomial τ R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    f (MvPolynomial.bind₁ g φ) = eval₂Hom (f.comp C) (fun i => f (g i)) φ := by
  rw [MvPolynomial.bind₁, map_aeval, algebraMap_eq]

