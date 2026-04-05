import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem optionEquivLeft_monomial (m : Option S₁ →₀ ℕ) (r : R) :
    MvPolynomial.optionEquivLeft R S₁ (monomial m r) = .monomial (m none) (monomial m.some r) := by
  rw [optionEquivLeft_apply, aeval_monomial, prod_option_index]
  · rw [MvPolynomial.monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.algebraMap_apply, algebraMap_eq, Option.elim_none, Option.elim_some,
      map_mul, mul_assoc]
    simp only [mul_comm, map_finsuppProd, map_pow]
  · simp
  · intros; rw [pow_add]

