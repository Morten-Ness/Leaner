import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_eq_bot {S : Subring R} : S.op = ⊥ ↔ S = ⊥ := Subring.op_injective.eq_iff' Subring.op_bot

