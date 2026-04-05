import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂_congr (g₁ g₂ : σ → S₁)
    (h : ∀ {i : σ} {c : σ →₀ ℕ}, i ∈ c.support → coeff c p ≠ 0 → g₁ i = g₂ i) :
    p.eval₂ f g₁ = p.eval₂ f g₂ := by
  apply Finset.sum_congr rfl
  intro C hc; dsimp; congr 1
  apply Finset.prod_congr rfl
  intro i hi; dsimp; congr 1
  apply h hi
  rwa [Finsupp.mem_support_iff] at hc

