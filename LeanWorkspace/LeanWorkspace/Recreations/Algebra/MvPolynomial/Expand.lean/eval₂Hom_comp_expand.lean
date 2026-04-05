import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem eval₂Hom_comp_expand (f : R →+* S) (g : σ → S) :
    (eval₂Hom f g).comp (MvPolynomial.expand p (σ := σ) (R := R) : MvPolynomial σ R →+* MvPolynomial σ R) =
      eval₂Hom f (g ^ p) := by
  ext <;> simp

