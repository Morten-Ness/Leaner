import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂_comp_left {S₂} [CommSemiring S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p) :
    k (MvPolynomial.eval₂ f g p) = MvPolynomial.eval₂ (k.comp f) (k ∘ g) p := by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [MvPolynomial.eval₂_add, k.map_add, MvPolynomial.eval₂_mul, k.map_mul]

