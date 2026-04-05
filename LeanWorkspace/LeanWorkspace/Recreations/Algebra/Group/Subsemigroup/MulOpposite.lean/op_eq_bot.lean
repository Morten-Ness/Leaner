import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_eq_bot {S : Subsemigroup M} : S.op = ⊥ ↔ S = ⊥ := Subsemigroup.op_injective.eq_iff' Subsemigroup.op_bot

