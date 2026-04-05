import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

variable (A B : GL n R)

theorem coe_one : ↑(1 : GL n R) = (1 : Matrix n n R) := rfl

