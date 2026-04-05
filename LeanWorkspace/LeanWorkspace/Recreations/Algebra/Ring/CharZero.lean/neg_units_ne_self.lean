import Mathlib

variable {α R S : Type*} {n : ℕ}

variable [Ring R] [CharZero R]

theorem neg_units_ne_self (u : Rˣ) : -u ≠ u := (units_ne_neg_self u).symm

