import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem Monic.leadingCoeff_C_mul (hp : p.Monic) (r : R) : (Polynomial.C r * p).leadingCoeff = r := by
  by_cases hr : r = 0 <;> simp_all [Polynomial.leadingCoeff_mul']

