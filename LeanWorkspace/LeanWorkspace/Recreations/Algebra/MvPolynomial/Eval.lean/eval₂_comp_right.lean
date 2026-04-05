import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem eval₂_comp_right {S₂} [CommSemiring S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p) :
    k (MvPolynomial.eval₂ f g p) = MvPolynomial.eval₂ k (k ∘ g) (MvPolynomial.map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [MvPolynomial.eval₂_C, MvPolynomial.map_C, MvPolynomial.eval₂_C]
  · intro p q hp hq
    rw [MvPolynomial.eval₂_add, k.map_add, (MvPolynomial.map f).map_add, MvPolynomial.eval₂_add, hp, hq]
  · intro p s hp
    rw [MvPolynomial.eval₂_mul, k.map_mul, (MvPolynomial.map f).map_mul, MvPolynomial.eval₂_mul, MvPolynomial.map_X, hp, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X, comp_apply]

