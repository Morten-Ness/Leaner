import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem map_eval₂Hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : φ (MvPolynomial.eval₂Hom f g p) = MvPolynomial.eval₂Hom (φ.comp f) (fun i => φ (g i)) p := by
  rw [← MvPolynomial.comp_eval₂Hom]
  rfl

