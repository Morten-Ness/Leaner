import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem C_add : (MvPolynomial.C (a + a') : MvPolynomial σ R) = MvPolynomial.C a + MvPolynomial.C a' := Finsupp.single_add _ _ _

