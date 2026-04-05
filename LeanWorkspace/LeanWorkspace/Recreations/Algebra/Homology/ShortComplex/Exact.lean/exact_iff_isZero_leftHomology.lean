import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_iff_isZero_leftHomology [S.HasHomology] :
    S.Exact ↔ IsZero S.leftHomology := CategoryTheory.ShortComplex.LeftHomologyData.exact_iff _

