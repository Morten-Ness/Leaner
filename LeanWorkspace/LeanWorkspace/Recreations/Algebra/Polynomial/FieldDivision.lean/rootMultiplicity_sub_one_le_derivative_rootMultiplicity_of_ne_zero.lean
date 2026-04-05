import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero
    (p : R[X]) (t : R) (hnezero : derivative p ≠ 0) :
    p.rootMultiplicity t - 1 ≤ p.derivative.rootMultiplicity t := (le_rootMultiplicity_iff hnezero).2 <|
    pow_sub_one_dvd_derivative_of_pow_dvd (p.pow_rootMultiplicity_dvd t)

