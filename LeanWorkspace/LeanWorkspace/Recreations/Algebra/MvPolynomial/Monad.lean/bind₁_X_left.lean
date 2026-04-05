import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

theorem bind₁_X_left : MvPolynomial.bind₁ (X : σ → MvPolynomial σ R) = AlgHom.id R _ := by
  ext1 i
  simp

