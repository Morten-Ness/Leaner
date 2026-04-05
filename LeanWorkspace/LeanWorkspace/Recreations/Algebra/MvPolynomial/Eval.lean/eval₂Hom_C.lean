import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂Hom_C (f : R →+* S₁) (g : σ → S₁) (r : R) : MvPolynomial.eval₂Hom f g (C r) = f r := MvPolynomial.eval₂_C f g r

