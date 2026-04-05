import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_X_mul (s : σ) (p : MvPolynomial σ R) :
    (MvPolynomial.X s * p).support = p.support.map (addLeftEmbedding (Finsupp.single s 1)) := AddMonoidAlgebra.support_single_mul p _ (by simp) _

