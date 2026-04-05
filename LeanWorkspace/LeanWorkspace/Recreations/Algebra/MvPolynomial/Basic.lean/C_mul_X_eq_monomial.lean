import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem C_mul_X_eq_monomial {s : σ} {a : R} : MvPolynomial.C a * MvPolynomial.X s = MvPolynomial.monomial (Finsupp.single s 1) a := by
  rw [← MvPolynomial.C_mul_X_pow_eq_monomial, pow_one]

