import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_eq_top {S : Subgroup G} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' Subgroup.op_top

