import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem smul_monomial {S₁ : Type*} [SMulZeroClass S₁ R] (r : S₁) :
    r • MvPolynomial.monomial s a = MvPolynomial.monomial s (r • a) := Finsupp.smul_single _ _ _

