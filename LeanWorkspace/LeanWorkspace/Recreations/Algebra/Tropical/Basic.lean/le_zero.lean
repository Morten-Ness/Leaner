import Mathlib

variable (R : Type u)

theorem le_zero [LE R] [OrderTop R] (x : Tropical R) : x ≤ 0 := le_top (α := R)

