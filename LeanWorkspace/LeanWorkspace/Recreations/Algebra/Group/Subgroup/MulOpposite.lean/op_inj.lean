import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_inj {S T : Subgroup G} : S.op = T.op ↔ S = T := Subgroup.opEquiv.eq_iff_eq

