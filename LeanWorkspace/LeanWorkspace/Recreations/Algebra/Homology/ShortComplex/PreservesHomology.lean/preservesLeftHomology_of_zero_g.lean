import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C)

set_option backward.isDefEq.respectTransparency false in
theorem preservesLeftHomology_of_zero_g (hg : S.g = 0)
    [PreservesColimit (parallelPair S.f 0) F] :
    F.PreservesLeftHomologyOf S := ⟨fun h =>
  { g := by
      rw [hg]
      infer_instance
    f' := by
      have := h.isIso_i hg
      let e : parallelPair h.f' 0 ≅ parallelPair S.f 0 :=
        parallelPair.ext (Iso.refl _) (asIso h.i) (by simp) (by simp)
      exact Limits.preservesColimit_of_iso_diagram F e.symm}⟩

