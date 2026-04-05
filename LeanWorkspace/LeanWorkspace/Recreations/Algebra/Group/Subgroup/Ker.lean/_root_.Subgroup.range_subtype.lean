import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem _root_.Subgroup.range_subtype (H : Subgroup G) : H.subtype.range = H := SetLike.coe_injective <| (MonoidHom.coe_range _).trans <| Subtype.range_coe

