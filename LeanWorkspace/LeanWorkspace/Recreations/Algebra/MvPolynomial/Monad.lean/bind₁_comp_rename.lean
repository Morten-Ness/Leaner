import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₁_comp_rename {υ : Type*} (f : τ → MvPolynomial υ R) (g : σ → τ) :
    (MvPolynomial.bind₁ f).comp (rename g) = MvPolynomial.bind₁ (f ∘ g) := by
  ext1 i
  simp

