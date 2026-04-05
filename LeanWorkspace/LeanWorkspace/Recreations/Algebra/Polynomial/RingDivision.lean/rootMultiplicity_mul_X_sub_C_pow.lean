import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem rootMultiplicity_mul_X_sub_C_pow {p : R[X]} {a : R} {n : ℕ} (h : p ≠ 0) :
    (p * (Polynomial.X - Polynomial.C a) ^ n).rootMultiplicity a = p.rootMultiplicity a + n := by
  have h2 := Polynomial.monic_X_sub_C a |>.pow n |>.mul_left_ne_zero h
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h2, add_assoc, add_comm n, ← add_assoc, pow_add,
      dvd_cancel_right_mem_nonZeroDivisors (Polynomial.monic_X_sub_C a |>.pow n |>.mem_nonZeroDivisors)]
    exact pow_rootMultiplicity_not_dvd h a
  · rw [le_rootMultiplicity_iff h2, pow_add]
    exact mul_dvd_mul_right (pow_rootMultiplicity_dvd p a) _

