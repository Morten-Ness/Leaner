import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem eval₂_comp (f : R →+* S₁) (g : σ → R) (p : MvPolynomial σ R) :
    f (MvPolynomial.eval g p) = MvPolynomial.eval₂ f (f ∘ g) p := by
  rw [← MvPolynomial.map_id p, MvPolynomial.eval_map, MvPolynomial.eval₂_comp_right]

