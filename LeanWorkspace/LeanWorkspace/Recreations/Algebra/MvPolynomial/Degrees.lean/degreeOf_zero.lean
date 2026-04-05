import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_zero (n : σ) : MvPolynomial.degreeOf n (0 : MvPolynomial σ R) = 0 := by
  classical simp only [MvPolynomial.degreeOf_def, MvPolynomial.degrees_zero, Multiset.count_zero]

