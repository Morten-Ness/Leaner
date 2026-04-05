import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem one_lt_rootMultiplicity_iff_isRoot_iterate_derivative
    {p : R[X]} {t : R} (h : p ≠ 0) :
    1 < p.rootMultiplicity t ↔ ∀ m ≤ 1, (derivative^[m] p).IsRoot t := Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors h
    (by rw [Nat.factorial_one, Nat.cast_one]; exact Submonoid.one_mem _)

