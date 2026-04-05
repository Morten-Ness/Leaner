import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem vars_monomial (h : r ≠ 0) : (monomial s r).vars = s.support := by
  classical rw [MvPolynomial.vars_def, degrees_monomial_eq _ _ h, Finsupp.toFinset_toMultiset]

