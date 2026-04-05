import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂_mul : ∀ {p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g := by
  apply MvPolynomial.induction_on q
  · simp [MvPolynomial.eval₂_C, MvPolynomial.eval₂_mul_C]
  · simp +contextual [mul_add, MvPolynomial.eval₂_add]
  · simp +contextual [X, MvPolynomial.eval₂_mul_monomial, ← mul_assoc]

