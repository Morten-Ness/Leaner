import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_injective {f : G →* N} (h : Function.Surjective f) : Function.Injective (comap f) := fun K L => by simp only [le_antisymm_iff, Subgroup.comap_le_comap_of_surjective h, imp_self]

