import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem rangeRestrict_surjective (f : G →* N) : Function.Surjective f.rangeRestrict := fun ⟨_, g, rfl⟩ => ⟨g, rfl⟩

