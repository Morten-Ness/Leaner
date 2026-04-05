import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p : R[X]}

theorem isUnit_leadingCoeff_mul_left_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} :
    q * p = 0 ↔ q = 0 := by
  constructor
  · intro hp
    replace hp := congr_arg (· * Polynomial.C ↑h.unit⁻¹) hp
    simp only [zero_mul] at hp
    rwa [mul_assoc, Polynomial.Monic.mul_left_eq_zero_iff] at hp
    refine Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    simp
  · rintro rfl
    rw [zero_mul]

