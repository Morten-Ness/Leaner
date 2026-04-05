import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem RightHomologyData.exact_iff [S.HasHomology]
    (h : S.RightHomologyData) :
    S.Exact ↔ IsZero h.H := by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

