import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem coe_set_mk {s : Submonoid G} (h_inv) :
    (Subgroup.mk s h_inv : Set G) = s := rfl

