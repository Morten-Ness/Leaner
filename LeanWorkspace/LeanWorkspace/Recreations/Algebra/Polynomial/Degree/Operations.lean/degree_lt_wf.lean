import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem degree_lt_wf : WellFounded fun p q : R[X] => degree p < degree q := InvImage.wf degree wellFounded_lt

