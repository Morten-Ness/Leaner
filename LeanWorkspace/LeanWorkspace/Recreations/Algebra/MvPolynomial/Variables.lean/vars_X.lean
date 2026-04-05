import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem vars_X [Nontrivial R] : (X n : MvPolynomial σ R).vars = {n} := by
  rw [X, MvPolynomial.vars_monomial (one_ne_zero' R), Finsupp.support_single_ne_zero _ (one_ne_zero' ℕ)]

