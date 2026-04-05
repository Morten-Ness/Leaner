import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem vars_C : (C r : MvPolynomial σ R).vars = ∅ := by
  classical rw [MvPolynomial.vars_def, degrees_C, Multiset.toFinset_zero]

