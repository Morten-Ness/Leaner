import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_C (a : R) (x : σ) : MvPolynomial.degreeOf x (C a : MvPolynomial σ R) = 0 := by
  classical simp [MvPolynomial.degreeOf_def, MvPolynomial.degrees_C]

