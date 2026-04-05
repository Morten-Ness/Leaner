import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable {A : Type*} [CommRing A] [NoZeroDivisors A]

theorem vars_C_mul (a : A) (ha : a ≠ 0) (φ : MvPolynomial σ A) :
    (C a * φ : MvPolynomial σ A).vars = φ.vars := by
  ext1 i
  simp only [MvPolynomial.mem_vars, mem_support_iff]
  apply exists_congr
  intro d
  rw [coeff_C_mul, mul_ne_zero_iff, eq_true ha, true_and]

