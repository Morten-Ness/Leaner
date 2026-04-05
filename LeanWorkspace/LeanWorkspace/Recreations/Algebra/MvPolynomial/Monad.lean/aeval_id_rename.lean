import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem aeval_id_rename (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    aeval id (rename f p) = aeval f p := by rw [aeval_rename, Function.id_comp]

