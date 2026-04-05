import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem subtype_comp_rangeRestrict (f : G →* N) : f.range.subtype.comp f.rangeRestrict = f := ext <| MonoidHom.coe_rangeRestrict f

