import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_X_pow [Nontrivial R] (s : σ) (n : ℕ) :
    (MvPolynomial.X s ^ n : MvPolynomial σ R).support = {Finsupp.single s n} := by
  classical
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.support_monomial, if_neg (one_ne_zero' R)]

