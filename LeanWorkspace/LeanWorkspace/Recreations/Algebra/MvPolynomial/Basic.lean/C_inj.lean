import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem C_inj {σ : Type*} (R : Type*) [CommSemiring R] (r s : R) :
    (MvPolynomial.C r : MvPolynomial σ R) = MvPolynomial.C s ↔ r = s := (MvPolynomial.C_injective σ R).eq_iff

