import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {f : σ → R}

theorem eval_assoc {τ} (f : σ → MvPolynomial τ R) (g : τ → R) (p : MvPolynomial σ R) :
    MvPolynomial.eval (MvPolynomial.eval g ∘ f) p = MvPolynomial.eval g (MvPolynomial.eval₂ C f p) := by
  rw [MvPolynomial.eval₂_comp_left (MvPolynomial.eval g)]
  unfold MvPolynomial.eval; simp only [MvPolynomial.coe_eval₂Hom]
  congr with a; simp

