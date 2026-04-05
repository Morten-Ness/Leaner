import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_eq_bot {S : Subsemiring R} : S.op = ⊥ ↔ S = ⊥ := Subsemiring.op_injective.eq_iff' Subsemiring.op_bot

