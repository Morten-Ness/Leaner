import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Field R] {p q : R[X]}

theorem isUnit_iff_degree_eq_zero : IsUnit p ↔ degree p = 0 := ⟨degree_eq_zero_of_isUnit, fun h =>
    have : degree p ≤ 0 := by simp [*]
    have hc : coeff p 0 ≠ 0 := fun hc => by
      rw [eq_C_of_degree_le_zero this, hc] at h; simp only [map_zero] at h; contradiction
    isUnit_iff_dvd_one.2
      ⟨Polynomial.C (coeff p 0)⁻¹, by
        conv in p => rw [eq_C_of_degree_le_zero this]
        rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩⟩

