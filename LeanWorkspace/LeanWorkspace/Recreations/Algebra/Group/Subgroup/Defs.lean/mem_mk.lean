import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem mem_mk {s : Submonoid G} {x : G} (h_inv) :
    x ∈ Subgroup.mk s h_inv ↔ x ∈ s := Iff.rfl

