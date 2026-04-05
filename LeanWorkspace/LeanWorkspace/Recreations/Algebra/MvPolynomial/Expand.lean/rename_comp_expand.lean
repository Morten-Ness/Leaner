import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem rename_comp_expand (f : σ → τ) :
    (rename f).comp (MvPolynomial.expand p) =
      (MvPolynomial.expand p).comp (rename f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) := by
  ext1 i
  simp

