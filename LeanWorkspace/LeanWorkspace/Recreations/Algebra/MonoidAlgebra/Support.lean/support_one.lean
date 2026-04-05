import Mathlib

open scoped Pointwise

variable {k : Type u₁} {G : Type u₂} [Semiring k]

theorem support_one [One G] [NeZero (1 : k)] : (1 : k[G]).support = 1 := Finsupp.support_single_ne_zero _ one_ne_zero

