import Mathlib

open scoped Pointwise

variable {k : Type u₁} {G : Type u₂} [Semiring k]

theorem support_one_subset [One G] : (1 : k[G]).support ⊆ 1 := Finsupp.support_single_subset

