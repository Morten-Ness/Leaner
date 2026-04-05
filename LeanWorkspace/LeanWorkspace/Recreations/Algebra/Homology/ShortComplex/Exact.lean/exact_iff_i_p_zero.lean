import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_iff_i_p_zero [S.HasHomology] (h₁ : S.LeftHomologyData)
    (h₂ : S.RightHomologyData) :
    S.Exact ↔ h₁.i ≫ h₂.p = 0 := (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂).exact_iff_i_p_zero

