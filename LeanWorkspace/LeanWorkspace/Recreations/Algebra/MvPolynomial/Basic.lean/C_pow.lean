import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem C_pow (a : R) (n : ℕ) : (MvPolynomial.C (a ^ n) : MvPolynomial σ R) = MvPolynomial.C a ^ n := map_pow _ _ _

