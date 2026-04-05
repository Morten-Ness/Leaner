import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem coe_toMultiplicative_range {A A' : Type*} [AddGroup A] [AddGroup A'] (f : A →+ A') :
    (AddMonoidHom.toMultiplicative f).range = AddSubgroup.toSubgroup f.range := rfl

