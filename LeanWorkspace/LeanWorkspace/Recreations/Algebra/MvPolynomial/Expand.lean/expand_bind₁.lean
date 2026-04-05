import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_bind₁ (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    MvPolynomial.expand p (bind₁ f φ) = bind₁ (fun i ↦ MvPolynomial.expand p (f i)) φ := by
  rw [← AlgHom.comp_apply, MvPolynomial.expand_comp_bind₁]

