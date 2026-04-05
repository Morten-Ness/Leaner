import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H : Type*} [Group H]

theorem coe_comapSubgroup (e : G ≃* H) : MulEquiv.comapSubgroup e = Subgroup.comap e.toMonoidHom := rfl

