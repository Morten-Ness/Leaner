import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem comap_mono {f : G →* N} {K K' : Subgroup N} : K ≤ K' → Subgroup.comap f K ≤ Subgroup.comap f K' := preimage_mono

