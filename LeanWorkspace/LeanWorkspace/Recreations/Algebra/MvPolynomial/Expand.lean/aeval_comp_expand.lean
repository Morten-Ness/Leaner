import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem aeval_comp_expand {A : Type*} [CommSemiring A] [Algebra R A] (f : σ → A) :
    (aeval f).comp (MvPolynomial.expand p) = aeval (R := R) (f ^ p) := by
  ext; simp

