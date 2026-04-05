import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem coeff_coe_units_zero_ne_zero [Nontrivial R] (u : R[X]ˣ) : coeff (u : R[X]) 0 ≠ 0 := by
  conv in 0 => rw [← natDegree_coe_units u]
  rw [← leadingCoeff, Ne, leadingCoeff_eq_zero]
  exact Units.ne_zero _

