import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem HomologyData.exact_iff' (h : S.HomologyData) :
    S.Exact ↔ IsZero h.right.H := by
  haveI := HasHomology.mk' h
  exact CategoryTheory.ShortComplex.RightHomologyData.exact_iff h.right

