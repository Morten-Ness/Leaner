import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

theorem killCompl_C (r : R) : MvPolynomial.killCompl hf (C r) = C r := algHom_C _ _

