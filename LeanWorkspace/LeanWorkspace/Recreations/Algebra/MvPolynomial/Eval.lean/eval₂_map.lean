import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem eval₂_map [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : MvPolynomial.eval₂ φ g (MvPolynomial.map f p) = MvPolynomial.eval₂ (φ.comp f) g p := by
  rw [← MvPolynomial.eval_map, ← MvPolynomial.eval_map, MvPolynomial.map_map]

