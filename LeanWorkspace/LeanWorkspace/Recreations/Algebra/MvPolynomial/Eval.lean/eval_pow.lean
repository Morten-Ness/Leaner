import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {f : σ → R}

theorem eval_pow : ∀ n, MvPolynomial.eval f (p ^ n) = MvPolynomial.eval f p ^ n := fun _ => MvPolynomial.eval₂_pow _ _

