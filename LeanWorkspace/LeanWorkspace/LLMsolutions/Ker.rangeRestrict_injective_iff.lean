FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem rangeRestrict_injective_iff {f : G →* N} : Function.Injective f.rangeRestrict ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    exact congrArg Subtype.val (h (Subtype.ext hxy))
  · intro h x y hxy
    exact h (congrArg Subtype.val hxy)
