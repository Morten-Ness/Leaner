import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

theorem eval₂Hom_id_X_eq_join₂ : eval₂Hom (RingHom.id _) X = @MvPolynomial.join₂ σ R _ := rfl

