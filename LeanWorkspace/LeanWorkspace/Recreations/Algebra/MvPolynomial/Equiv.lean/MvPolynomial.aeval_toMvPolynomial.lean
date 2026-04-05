import Mathlib

open scoped Polynomial

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem MvPolynomial.aeval_toMvPolynomial (f : σ → S) (i : σ) (p : R[X]) :
    Polynomial.aeval f (p.toMvPolynomial i) = Polynomial.aeval (f i) p := DFunLike.congr_fun (aeval_comp_toMvPolynomial ..) p

