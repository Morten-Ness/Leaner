import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

variable [NoZeroDivisors R]

theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity [CharZero R] (p : R[X]) (t : R) :
    p.rootMultiplicity t - 1 ≤ p.derivative.rootMultiplicity t := by
  by_cases h : p.IsRoot t
  · exact (Polynomial.derivative_rootMultiplicity_of_root h).symm.le
  · rw [rootMultiplicity_eq_zero h, zero_tsub]
    exact zero_le _

