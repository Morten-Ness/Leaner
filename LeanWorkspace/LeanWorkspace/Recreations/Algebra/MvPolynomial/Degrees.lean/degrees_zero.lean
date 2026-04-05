import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_zero : MvPolynomial.degrees (0 : MvPolynomial σ R) = 0 := by
  rw [← C_0]
  exact MvPolynomial.degrees_C 0

