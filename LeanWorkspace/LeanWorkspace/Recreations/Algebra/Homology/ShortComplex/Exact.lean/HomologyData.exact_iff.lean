import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem HomologyData.exact_iff (h : S.HomologyData) :
    S.Exact ↔ IsZero h.left.H := by
  haveI := HasHomology.mk' h
  exact CategoryTheory.ShortComplex.LeftHomologyData.exact_iff h.left

