import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_iInf (S : ι → Submonoid M) : (iInf S).op = ⨅ i, (S i).op := Submonoid.opEquiv.map_iInf _

