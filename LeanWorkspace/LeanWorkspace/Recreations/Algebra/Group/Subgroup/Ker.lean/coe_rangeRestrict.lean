import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem coe_rangeRestrict (f : G →* N) (g : G) : (f.rangeRestrict g : N) = f g := rfl

