import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem surjOn_iff_le_map {f : G →* N} {H : Subgroup G} {K : Subgroup N} :
    Set.SurjOn f H K ↔ K ≤ H.map f := Iff.rfl

