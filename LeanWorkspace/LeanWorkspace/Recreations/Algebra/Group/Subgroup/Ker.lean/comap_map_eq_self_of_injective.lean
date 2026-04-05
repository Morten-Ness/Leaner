import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_map_eq_self_of_injective {f : G →* N} (h : Function.Injective f) (H : Subgroup G) :
    comap f (map f H) = H := Subgroup.comap_map_eq_self (((MonoidHom.ker_eq_bot_iff _).mpr h).symm ▸ bot_le)

