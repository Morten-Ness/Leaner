import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_monomial_eq (s : σ →₀ ℕ) (a : R) (ha : a ≠ 0) :
    MvPolynomial.degrees (monomial s a) = toMultiset s := by
  classical
    exact (supDegree_single s a).trans (if_neg ha)

