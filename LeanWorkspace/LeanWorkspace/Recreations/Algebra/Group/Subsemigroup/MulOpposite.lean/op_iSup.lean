import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_iSup (S : ι → Subsemigroup M) : (iSup S).op = ⨆ i, (S i).op := Subsemigroup.opEquiv.map_iSup _

