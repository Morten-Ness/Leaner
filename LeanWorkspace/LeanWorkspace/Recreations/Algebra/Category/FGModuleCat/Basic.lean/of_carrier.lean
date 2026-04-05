import Mathlib

variable (R : Type u) [Ring R]

theorem of_carrier (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V] :
    of R V = V := rfl

