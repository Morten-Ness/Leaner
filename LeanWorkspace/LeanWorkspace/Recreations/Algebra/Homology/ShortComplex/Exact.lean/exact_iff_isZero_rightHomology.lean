import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_iff_isZero_rightHomology [S.HasHomology] :
    S.Exact ↔ IsZero S.rightHomology := CategoryTheory.ShortComplex.RightHomologyData.exact_iff _

