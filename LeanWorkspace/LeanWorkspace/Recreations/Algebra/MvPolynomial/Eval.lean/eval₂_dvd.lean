import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂_dvd (f : R →+* S₁) (g : σ → S₁) {p q : MvPolynomial σ R} (h : p ∣ q) :
    p.eval₂ f g ∣ q.eval₂ f g := map_dvd (MvPolynomial.eval₂Hom f g) h

