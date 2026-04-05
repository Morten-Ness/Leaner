import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem notMem_support_iff {p : MvPolynomial σ R} {m : σ →₀ ℕ} : m ∉ p.support ↔ p.coeff m = 0 := by
  simp

