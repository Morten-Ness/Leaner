import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem coe_inclusion {H K : Subgroup G} (h : H ≤ K) (a : H) : (Subgroup.inclusion h a : G) = a := Set.coe_inclusion h a

