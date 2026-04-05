import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_iff_iCycles_pOpcycles_zero [S.HasHomology] :
    S.Exact ↔ S.iCycles ≫ S.pOpcycles = 0 := S.exact_iff_i_p_zero _ _

