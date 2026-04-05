import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_iSup (S : ι → Submonoid M) : (iSup S).op = ⨆ i, (S i).op := Submonoid.opEquiv.map_iSup _

