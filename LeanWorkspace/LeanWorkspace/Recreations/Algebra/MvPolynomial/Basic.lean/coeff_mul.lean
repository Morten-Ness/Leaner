import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_mul [DecidableEq σ] (p q : MvPolynomial σ R) (n : σ →₀ ℕ) :
    MvPolynomial.coeff n (p * q) = ∑ x ∈ Finset.antidiagonal n, MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q := AddMonoidAlgebra.mul_apply_antidiagonal p q _ _ Finset.mem_antidiagonal

