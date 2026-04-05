import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂Hom_smul (f : R →+* S₁) (g : σ → S₁) (r : R) (P : MvPolynomial σ R) :
    MvPolynomial.eval₂Hom f g (r • P) = f r • MvPolynomial.eval₂Hom f g P := by
  simp [smul_eq_C_mul]

