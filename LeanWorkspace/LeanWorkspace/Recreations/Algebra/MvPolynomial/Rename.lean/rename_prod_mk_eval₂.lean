import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

theorem rename_prod_mk_eval₂ (j : τ) (g : σ → MvPolynomial σ R) :
    MvPolynomial.rename (Prod.mk j) (p.eval₂ C g) = p.eval₂ C fun x => MvPolynomial.rename (Prod.mk j) (g x) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

