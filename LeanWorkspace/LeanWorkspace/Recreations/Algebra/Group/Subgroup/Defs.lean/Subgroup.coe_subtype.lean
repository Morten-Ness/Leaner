import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem coe_subtype : ⇑H.subtype = ((↑) : H → G) := rfl

