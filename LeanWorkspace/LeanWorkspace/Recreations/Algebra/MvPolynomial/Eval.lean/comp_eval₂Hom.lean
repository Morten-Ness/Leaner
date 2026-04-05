import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem comp_eval₂Hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂) :
    φ.comp (MvPolynomial.eval₂Hom f g) = MvPolynomial.eval₂Hom (φ.comp f) fun i => φ (g i) := by
  ext <;> simp

