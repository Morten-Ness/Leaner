import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_add_le (n : σ) (f g : MvPolynomial σ R) :
    MvPolynomial.degreeOf n (f + g) ≤ max (MvPolynomial.degreeOf n f) (MvPolynomial.degreeOf n g) := by
  simp_rw [MvPolynomial.degreeOf_eq_sup]; exact supDegree_add_le

