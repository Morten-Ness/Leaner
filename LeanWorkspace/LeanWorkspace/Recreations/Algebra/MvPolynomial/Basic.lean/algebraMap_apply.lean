import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem algebraMap_apply [Algebra R S₁] (r : R) :
    algebraMap R (MvPolynomial σ S₁) r = MvPolynomial.C (algebraMap R S₁ r) := rfl

