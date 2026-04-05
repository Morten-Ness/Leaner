import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_X' [DecidableEq σ] (i : σ) (m) :
    MvPolynomial.coeff m (MvPolynomial.X i : MvPolynomial σ R) = if Finsupp.single i 1 = m then 1 else 0 := by
  rw [← MvPolynomial.coeff_X_pow, pow_one]

