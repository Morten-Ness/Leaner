import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

theorem aeval_rename [Algebra R S] : aeval g (MvPolynomial.rename k p) = aeval (g ∘ k) p := MvPolynomial.eval₂Hom_rename _ _ _ _

