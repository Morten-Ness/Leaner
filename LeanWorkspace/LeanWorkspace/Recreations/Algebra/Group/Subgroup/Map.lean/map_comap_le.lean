import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (f : G →* N)

theorem map_comap_le (H : Subgroup N) : Subgroup.map f (Subgroup.comap f H) ≤ H := (Subgroup.gc_map_comap f).l_u_le _

