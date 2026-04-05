import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₁_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R)
    (φ : MvPolynomial σ R) : (MvPolynomial.bind₁ g) (MvPolynomial.bind₁ f φ) = MvPolynomial.bind₁ (fun i => MvPolynomial.bind₁ g (f i)) φ := by
  simp [MvPolynomial.bind₁, ← comp_aeval]

