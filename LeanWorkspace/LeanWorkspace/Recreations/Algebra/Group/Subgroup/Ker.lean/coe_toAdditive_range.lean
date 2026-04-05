import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem coe_toAdditive_range (f : G →* G') :
    (MonoidHom.toAdditive f).range = Subgroup.toAddSubgroup f.range := rfl

