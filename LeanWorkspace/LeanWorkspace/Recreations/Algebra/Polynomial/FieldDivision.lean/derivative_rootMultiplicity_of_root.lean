import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

variable [NoZeroDivisors R]

theorem derivative_rootMultiplicity_of_root [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t) :
    p.derivative.rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · rw [h, map_zero, rootMultiplicity_zero]
  exact Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hpt <|
    mem_nonZeroDivisors_of_ne_zero <| Nat.cast_ne_zero.2 ((rootMultiplicity_pos h).2 hpt).ne'

