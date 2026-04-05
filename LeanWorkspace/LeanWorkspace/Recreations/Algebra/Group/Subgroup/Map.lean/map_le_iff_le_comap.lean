import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_le_iff_le_comap {f : G →* N} {K : Subgroup G} {H : Subgroup N} :
    K.map f ≤ H ↔ K ≤ H.comap f := image_subset_iff

