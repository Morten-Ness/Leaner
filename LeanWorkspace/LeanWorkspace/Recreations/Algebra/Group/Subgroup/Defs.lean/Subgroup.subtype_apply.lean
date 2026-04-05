import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem subtype_apply {s : Subgroup G} (x : s) :
    s.subtype x = x := rfl

