import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem rangeRestrict_injective_iff {f : G →* N} : Function.Injective f.rangeRestrict ↔ Function.Injective f := by
  convert Set.injective_codRestrict _

