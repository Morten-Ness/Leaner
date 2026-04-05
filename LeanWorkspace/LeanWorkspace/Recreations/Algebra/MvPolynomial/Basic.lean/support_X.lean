import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_X [Nontrivial R] : (MvPolynomial.X n : MvPolynomial σ R).support = {Finsupp.single n 1} := by
  classical rw [MvPolynomial.X, MvPolynomial.support_monomial, if_neg]; exact one_ne_zero

