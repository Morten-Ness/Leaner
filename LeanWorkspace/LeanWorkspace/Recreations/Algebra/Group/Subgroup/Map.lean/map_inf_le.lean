import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_inf_le (H K : Subgroup G) (f : G →* N) : Subgroup.map f (H ⊓ K) ≤ Subgroup.map f H ⊓ Subgroup.map f K := le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)

