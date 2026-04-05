import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_comap_eq_self_of_surjective {f : G →* N} (h : Function.Surjective f) (H : Subgroup N) :
    map f (comap f H) = H := Subgroup.map_comap_eq_self (MonoidHom.range_eq_top.2 h ▸ le_top)

