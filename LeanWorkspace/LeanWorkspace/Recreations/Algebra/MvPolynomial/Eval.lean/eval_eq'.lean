import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {f : σ → R}

theorem eval_eq' [Fintype σ] (X : σ → R) (f : MvPolynomial σ R) :
    MvPolynomial.eval X f = ∑ d ∈ f.support, f.coeff d * ∏ i, X i ^ d i := MvPolynomial.eval₂_eq' (RingHom.id R) X f

