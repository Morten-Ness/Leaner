import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem map_bind₁ (f : R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    map f (MvPolynomial.bind₁ g φ) = MvPolynomial.bind₁ (fun i : σ => (map f) (g i)) (map f φ) := by
  rw [MvPolynomial.hom_bind₁, MvPolynomial.map_comp_C, ← eval₂Hom_map_hom]
  rfl

