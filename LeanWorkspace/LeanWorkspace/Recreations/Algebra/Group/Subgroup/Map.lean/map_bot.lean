import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_bot (f : G →* N) : (⊥ : Subgroup G).map f = ⊥ := (Subgroup.gc_map_comap f).l_bot

