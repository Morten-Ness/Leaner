import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_eq_top {S : Submonoid M} : S.op = ⊤ ↔ S = ⊤ := Submonoid.op_injective.eq_iff' Submonoid.op_top

