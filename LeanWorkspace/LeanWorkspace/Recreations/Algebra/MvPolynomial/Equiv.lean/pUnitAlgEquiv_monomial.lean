import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem pUnitAlgEquiv_monomial {d : PUnit →₀ ℕ} {r : R} :
    MvPolynomial.pUnitAlgEquiv R (MvPolynomial.monomial d r)
      = Polynomial.monomial (d ()) r := by
  simp [Polynomial.C_mul_X_pow_eq_monomial]

