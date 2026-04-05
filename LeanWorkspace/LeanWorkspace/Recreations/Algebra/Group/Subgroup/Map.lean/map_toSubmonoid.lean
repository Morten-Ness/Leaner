import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_toSubmonoid (f : G →* G') (K : Subgroup G) :
    (Subgroup.map f K).toSubmonoid = Submonoid.map f K.toSubmonoid := rfl

