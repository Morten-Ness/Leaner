import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H : Type*} [Group H]

theorem coe_mapSubgroup (e : G ≃* H) : MulEquiv.mapSubgroup e = Subgroup.map e.toMonoidHom := rfl

