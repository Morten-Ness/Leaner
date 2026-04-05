import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_iInf (S : ι → Subsemigroup M) : (iInf S).op = ⨅ i, (S i).op := Subsemigroup.opEquiv.map_iInf _

