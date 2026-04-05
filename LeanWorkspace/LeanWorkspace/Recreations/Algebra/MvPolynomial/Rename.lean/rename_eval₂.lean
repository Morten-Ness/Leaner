import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

theorem rename_eval₂ (g : τ → MvPolynomial σ R) :
    MvPolynomial.rename k (p.eval₂ C (g ∘ k)) = (MvPolynomial.rename k p).eval₂ C (MvPolynomial.rename k ∘ g) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

