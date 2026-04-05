import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_comp_bind₁ (p : ℕ) (f : σ → MvPolynomial τ R) :
    (MvPolynomial.expand p).comp (bind₁ f) = bind₁ fun i ↦ MvPolynomial.expand p (f i) := by
  ext1 i
  simp

