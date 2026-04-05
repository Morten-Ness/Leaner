import Mathlib

variable {R : Type*}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R] [NoZeroDivisors R] {p q r : MvPolynomial σ R}

theorem dvd_X_iff_exists {i : σ} :
    p ∣ X i ↔ ∃ r, IsUnit r ∧ (p = C r ∨ p = r • X i) := by
  nontriviality R
  rw [← one_smul R (X i), MvPolynomial.dvd_smul_X_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro r
  rw [isUnit_iff_dvd_one, one_smul]

