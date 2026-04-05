import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable {K : Type*} [DivisionRing K]

theorem monic_mul_leadingCoeff_inv {p : K[X]} (h : p ≠ 0) : Polynomial.Monic (p * Polynomial.C (leadingCoeff p)⁻¹) := by
  rw [Polynomial.Monic, leadingCoeff_mul, leadingCoeff_C,
    mul_inv_cancel₀ (show leadingCoeff p ≠ 0 from mt leadingCoeff_eq_zero.1 h)]

-- `simp` normal form of `degree_mul_leadingCoeff_inv`

