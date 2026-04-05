import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

theorem aeval_id_eq_join₁ : aeval id = @MvPolynomial.join₁ σ R _ := rfl

