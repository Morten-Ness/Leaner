import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem coe_toMultiplicative_ker {A A' : Type*} [AddGroup A] [AddZeroClass A'] (f : A →+ A') :
    (AddMonoidHom.toMultiplicative f).ker = AddSubgroup.toSubgroup f.ker := rfl

