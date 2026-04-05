import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_le_range (H : Subgroup G) : map f H ≤ f.range := (MonoidHom.range_eq_map f).symm ▸ map_mono le_top

