import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

variable [NoZeroDivisors R]

theorem lt_rootMultiplicity_of_isRoot_iterate_derivative
    [CharZero R] {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hroot : ∀ m ≤ n, (derivative^[m] p).IsRoot t) :
    n < p.rootMultiplicity t := Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot <|
    mem_nonZeroDivisors_of_ne_zero <| Nat.cast_ne_zero.2 <| by positivity

