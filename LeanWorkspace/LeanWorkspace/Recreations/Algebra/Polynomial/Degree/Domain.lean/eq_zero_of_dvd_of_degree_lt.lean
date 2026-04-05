import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem eq_zero_of_dvd_of_degree_lt (h₁ : p ∣ q) (h₂ : degree q < degree p) : q = 0 := by
  by_contra hc
  exact lt_iff_not_ge.mp h₂ (Polynomial.degree_le_of_dvd h₁ hc)

