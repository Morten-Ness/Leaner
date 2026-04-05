import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_inj {S T : Submonoid M} : S.op = T.op ↔ S = T := Submonoid.opEquiv.eq_iff_eq

