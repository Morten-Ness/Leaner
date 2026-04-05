import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem coe_toAdditive_ker (f : G →* G') :
    (MonoidHom.toAdditive f).ker = Subgroup.toAddSubgroup f.ker := rfl

