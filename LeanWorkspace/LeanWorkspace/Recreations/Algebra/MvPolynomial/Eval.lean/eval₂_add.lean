import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g := by
  classical exact Finsupp.sum_add_index (by simp [f.map_zero]) (by simp [add_mul, f.map_add])

