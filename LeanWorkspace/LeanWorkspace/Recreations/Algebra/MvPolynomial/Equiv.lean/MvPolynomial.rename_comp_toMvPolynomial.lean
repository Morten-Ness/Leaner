import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem MvPolynomial.rename_comp_toMvPolynomial (f : σ → τ) (a : σ) :
    (rename (R := R) f).comp (Polynomial.toMvPolynomial a) = Polynomial.toMvPolynomial (f a) := by
  ext
  simp

