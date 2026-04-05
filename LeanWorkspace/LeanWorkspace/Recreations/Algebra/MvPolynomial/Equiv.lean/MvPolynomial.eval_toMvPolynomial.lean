import Mathlib

open scoped Polynomial

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem MvPolynomial.eval_toMvPolynomial (f : σ → R) (i : σ) (p : R[X]) :
    eval f (p.toMvPolynomial i) = Polynomial.eval (f i) p := DFunLike.congr_fun (eval_comp_toMvPolynomial ..) p

