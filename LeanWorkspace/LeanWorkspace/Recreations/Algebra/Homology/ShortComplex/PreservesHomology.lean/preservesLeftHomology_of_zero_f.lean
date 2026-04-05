import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C)

theorem preservesLeftHomology_of_zero_f (hf : S.f = 0)
    [PreservesLimit (parallelPair S.g 0) F] :
    F.PreservesLeftHomologyOf S := ⟨fun h =>
  { g := by infer_instance
    f' := Limits.preservesCokernel_zero' _ _
      (by rw [← cancel_mono h.i, h.f'_i, zero_comp, hf]) }⟩

