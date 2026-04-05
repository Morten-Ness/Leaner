import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂_X_pow {s : σ} {n : ℕ} : ((X s) ^ n).eval₂ f g = (g s) ^ n := by
  simp [X_pow_eq_monomial, MvPolynomial.eval₂_monomial f g]

