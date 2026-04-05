import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_mul_X (s : σ) (p : MvPolynomial σ R) :
    (p * MvPolynomial.X s).support = p.support.map (addRightEmbedding (Finsupp.single s 1)) := AddMonoidAlgebra.support_mul_single p _ (by simp) _

