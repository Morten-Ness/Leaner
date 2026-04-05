import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

theorem killCompl_rename_app (p : MvPolynomial σ R) : MvPolynomial.killCompl hf (MvPolynomial.rename f p) = p := AlgHom.congr_fun (MvPolynomial.killCompl_comp_rename hf) p

