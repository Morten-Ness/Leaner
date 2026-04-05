import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_mul_monic {p q : R[X]} (hq : Polynomial.Monic q) :
    leadingCoeff (p * q) = leadingCoeff p := letI := Classical.decEq R
  Decidable.byCases
    (fun H : leadingCoeff p = 0 => by
      rw [H, leadingCoeff_eq_zero.1 H, zero_mul, leadingCoeff_zero])
    fun H : leadingCoeff p ≠ 0 => by
      rw [Polynomial.leadingCoeff_mul', hq.leadingCoeff, mul_one]
      rwa [hq.leadingCoeff, mul_one]

