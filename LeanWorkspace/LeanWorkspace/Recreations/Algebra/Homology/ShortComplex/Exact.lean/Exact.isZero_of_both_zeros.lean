import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem Exact.isZero_of_both_zeros (ex : S.Exact) (hf : S.f = 0) (hg : S.g = 0) :
    IsZero S.X₂ := (CategoryTheory.ShortComplex.HomologyData.ofZeros S hf hg).exact_iff.1 ex

