import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂_eta (p : MvPolynomial σ R) : MvPolynomial.eval₂ C X p = p := by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul]

