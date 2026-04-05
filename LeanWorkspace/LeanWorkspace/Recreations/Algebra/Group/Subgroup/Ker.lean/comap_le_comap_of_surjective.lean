import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_le_comap_of_surjective {f : G →* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f ≤ L.comap f ↔ K ≤ L := Subgroup.comap_le_comap_of_le_range (MonoidHom.range_eq_top.2 hf ▸ le_top)

