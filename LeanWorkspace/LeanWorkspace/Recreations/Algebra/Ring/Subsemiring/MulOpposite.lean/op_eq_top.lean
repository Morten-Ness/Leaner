import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_eq_top {S : Subsemiring R} : S.op = ⊤ ↔ S = ⊤ := Subsemiring.op_injective.eq_iff' Subsemiring.op_top

