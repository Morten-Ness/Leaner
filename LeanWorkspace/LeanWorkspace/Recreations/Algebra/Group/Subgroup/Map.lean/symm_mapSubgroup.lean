import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H : Type*} [Group H]

theorem symm_mapSubgroup (e : G ≃* H) : (MulEquiv.mapSubgroup e).symm = MulEquiv.mapSubgroup e.symm := rfl

