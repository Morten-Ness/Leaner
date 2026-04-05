import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C)

set_option backward.isDefEq.respectTransparency false in
theorem preservesRightHomology_of_zero_f (hf : S.f = 0)
    [PreservesLimit (parallelPair S.g 0) F] :
    F.PreservesRightHomologyOf S := ⟨fun h =>
  { f := by
      rw [hf]
      infer_instance
    g' := by
      have := h.isIso_p hf
      let e : parallelPair S.g 0 ≅ parallelPair h.g' 0 :=
        parallelPair.ext (asIso h.p) (Iso.refl _) (by simp) (by simp)
      exact Limits.preservesLimit_of_iso_diagram F e }⟩

