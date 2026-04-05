import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem map_eval {S₂ : Type*} [CommSemiring S₂] (q : S₁ →+* S₂) (g : σ → S₁) (p : MvPolynomial σ S₁) :
    q (MvPolynomial.eval g p) = MvPolynomial.eval (q ∘ g) (MvPolynomial.map q p) := by
  rw [← MvPolynomial.eval₂_eq_eval_map, ← MvPolynomial.eval₂_id, MvPolynomial.eval₂_comp_right, MvPolynomial.map_id]

