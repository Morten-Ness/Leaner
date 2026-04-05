import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_injective : (@Subgroup.op G _).Injective := Subgroup.opEquiv.injective

