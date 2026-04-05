import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem degree_coe_units [Nontrivial R] (u : R[X]ˣ) : degree (u : R[X]) = 0 := Polynomial.degree_eq_zero_of_isUnit ⟨u, rfl⟩

