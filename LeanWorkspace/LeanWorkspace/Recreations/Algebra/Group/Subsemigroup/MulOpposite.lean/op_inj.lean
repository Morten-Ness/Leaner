import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_inj {S T : Subsemigroup M} : S.op = T.op ↔ S = T := Subsemigroup.opEquiv.eq_iff_eq

