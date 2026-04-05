import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem monomial_single_add : MvPolynomial.monomial (Finsupp.single n e + s) a = MvPolynomial.X n ^ e * MvPolynomial.monomial s a := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]

