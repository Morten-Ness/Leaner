import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_rangeRestrict (f : G →* N) : MonoidHom.ker (MonoidHom.rangeRestrict f) = MonoidHom.ker f := MonoidHom.ker_codRestrict _ _ _

