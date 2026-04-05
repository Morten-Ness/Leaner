import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem mk_le_mk {s t : Submonoid G} (h_inv) (h_inv') :
    Subgroup.mk s h_inv ≤ Subgroup.mk t h_inv' ↔ s ≤ t := Iff.rfl

