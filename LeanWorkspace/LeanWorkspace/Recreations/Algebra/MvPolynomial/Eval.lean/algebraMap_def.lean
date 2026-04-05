import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem algebraMap_def :
    algebraMap (MvPolynomial σ R) (MvPolynomial σ S) = MvPolynomial.map (algebraMap R S) := rfl

