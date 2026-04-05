import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem C_mul_monomial : MvPolynomial.C a * MvPolynomial.monomial s a' = MvPolynomial.monomial s (a * a') := by
  have := single_mul_single 0 s a a'
  rw [zero_add] at this
  exact this

