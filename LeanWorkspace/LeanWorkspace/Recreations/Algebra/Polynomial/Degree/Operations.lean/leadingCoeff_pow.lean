import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

variable [NoZeroDivisors R] {p q : R[X]}

theorem leadingCoeff_pow (p : R[X]) (n : ℕ) : leadingCoeff (p ^ n) = leadingCoeff p ^ n := (Polynomial.leadingCoeffHom : R[X] →* R).map_pow p n

