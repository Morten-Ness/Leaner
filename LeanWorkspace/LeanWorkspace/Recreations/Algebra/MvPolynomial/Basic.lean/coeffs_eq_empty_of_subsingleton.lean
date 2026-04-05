import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeffs_eq_empty_of_subsingleton [Subsingleton R] (p : MvPolynomial σ R) : p.coeffs = ∅ := by
  simpa [MvPolynomial.coeffs] using Subsingleton.eq_zero p

