import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem ne_zero_iff {p : MvPolynomial σ R} : p ≠ 0 ↔ ∃ d, MvPolynomial.coeff d p ≠ 0 := by
  rw [Ne, MvPolynomial.eq_zero_iff]
  push Not
  rfl

