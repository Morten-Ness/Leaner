import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

theorem degreeOf_sub_le (i : σ) (p q : MvPolynomial σ R) :
    degreeOf i (p - q) ≤ max (degreeOf i p) (degreeOf i q) := by
  simpa only [sub_eq_add_neg, MvPolynomial.degreeOf_neg] using degreeOf_add_le i p (-q)

