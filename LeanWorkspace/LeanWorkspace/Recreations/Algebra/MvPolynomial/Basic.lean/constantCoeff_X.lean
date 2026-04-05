import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem constantCoeff_X (i : σ) : MvPolynomial.constantCoeff (MvPolynomial.X i : MvPolynomial σ R) = 0 := by
  simp [MvPolynomial.constantCoeff_eq]

