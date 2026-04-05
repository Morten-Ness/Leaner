import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable {K : Type*} [DivisionRing K]

theorem irreducible_mul_leadingCoeff_inv {p : K[X]} :
    Irreducible (p * Polynomial.C (leadingCoeff p)⁻¹) ↔ Irreducible p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact irreducible_mul_isUnit
    (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))

