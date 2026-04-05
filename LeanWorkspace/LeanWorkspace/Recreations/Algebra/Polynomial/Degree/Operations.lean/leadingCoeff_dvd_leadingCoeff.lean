import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

variable [NoZeroDivisors R] {p q : R[X]}

theorem leadingCoeff_dvd_leadingCoeff {a p : R[X]} (hap : a ∣ p) :
    a.leadingCoeff ∣ p.leadingCoeff := map_dvd Polynomial.leadingCoeffHom hap

