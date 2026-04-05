import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem MvPolynomial.aeval_comp_toMvPolynomial (f : σ → S) (i : σ) :
    (Polynomial.aeval (R := R) f).comp (toMvPolynomial i) = Polynomial.aeval (f i) := by
  ext
  simp

