import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem subgroupMap_surjective (f : G →* G') (H : Subgroup G) :
    Function.Surjective (f.subgroupMap H) := f.submonoidMap_surjective H.toSubmonoid

