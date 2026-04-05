import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_injective : (@Subgroup.unop G _).Injective := Subgroup.opEquiv.symm.injective

