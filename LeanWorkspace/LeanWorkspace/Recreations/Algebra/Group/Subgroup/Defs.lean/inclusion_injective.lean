import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem inclusion_injective {H K : Subgroup G} (h : H ≤ K) : Function.Injective <| Subgroup.inclusion h := Set.inclusion_injective h

