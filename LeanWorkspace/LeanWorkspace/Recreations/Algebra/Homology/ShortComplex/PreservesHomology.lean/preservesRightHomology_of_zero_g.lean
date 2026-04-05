import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C)

theorem preservesRightHomology_of_zero_g (hg : S.g = 0)
    [PreservesColimit (parallelPair S.f 0) F] :
    F.PreservesRightHomologyOf S := ⟨fun h =>
  { f := by infer_instance
    g' := Limits.preservesKernel_zero' _ _
      (by rw [← cancel_epi h.p, h.p_g', comp_zero, hg]) }⟩

