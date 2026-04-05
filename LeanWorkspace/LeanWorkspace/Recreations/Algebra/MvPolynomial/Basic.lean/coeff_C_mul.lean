import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_C_mul (m) (a : R) (p : MvPolynomial σ R) : MvPolynomial.coeff m (MvPolynomial.C a * p) = a * MvPolynomial.coeff m p := by
  classical
  rw [MvPolynomial.mul_def, MvPolynomial.sum_C]
  · simp +contextual [MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  simp

