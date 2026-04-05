import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem comap_top (f : G →* N) : (⊤ : Subgroup N).comap f = ⊤ := (Subgroup.gc_map_comap f).u_top

