import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

theorem aeval_comp_rename [Algebra R S] :
    (aeval (R := R) g).comp (MvPolynomial.rename k) = MvPolynomial.aeval (g ∘ k) :=
  AlgHom.ext fun p ↦ MvPolynomial.aeval_rename k g p

