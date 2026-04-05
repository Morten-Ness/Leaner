import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem constantCoeff_smul {R : Type*} [SMulZeroClass R S₁] (a : R) (f : MvPolynomial σ S₁) :
    MvPolynomial.constantCoeff (a • f) = a • MvPolynomial.constantCoeff f := rfl

