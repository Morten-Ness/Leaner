import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_smul {S₁ : Type*} [SMulZeroClass S₁ R] (m : σ →₀ ℕ) (MvPolynomial.C : S₁) (p : MvPolynomial σ R) :
    MvPolynomial.coeff m (MvPolynomial.C • p) = MvPolynomial.C • MvPolynomial.coeff m p := AddMonoidAlgebra.smul_apply MvPolynomial.C p m

