import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_injective {f : G →* N} (h : Function.Injective f) : Function.Injective (map f) := Function.LeftInverse.injective <| Subgroup.comap_map_eq_self_of_injective h

