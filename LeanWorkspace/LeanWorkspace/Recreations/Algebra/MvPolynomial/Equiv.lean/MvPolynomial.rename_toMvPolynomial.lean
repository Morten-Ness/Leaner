import Mathlib

open scoped Polynomial

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem MvPolynomial.rename_toMvPolynomial (f : σ → τ) (a : σ) (p : R[X]) :
    (rename (R := R) f) (p.toMvPolynomial a) = p.toMvPolynomial (f a) :=
  DFunLike.congr_fun (rename_comp_toMvPolynomial ..) p

