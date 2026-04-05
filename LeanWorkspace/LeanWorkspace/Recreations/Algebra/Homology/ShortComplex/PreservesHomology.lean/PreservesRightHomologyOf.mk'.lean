import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable (F : C ⥤ D) [PreservesZeroMorphisms F] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

theorem PreservesRightHomologyOf.mk' (h : S.RightHomologyData) [h.IsPreservedBy F] :
    F.PreservesRightHomologyOf S where
  isPreservedBy h' := { f := ShortComplex.RightHomologyData.IsPreservedBy.hf h F
      g' := by
        have := ShortComplex.RightHomologyData.IsPreservedBy.hg' h F
        let e : parallelPair h.g' 0 ≅ parallelPair h'.g' 0 :=
          parallelPair.ext (ShortComplex.opcyclesMapIso' (Iso.refl S) h h') (Iso.refl _)
            (by simp) (by simp)
        exact preservesLimit_of_iso_diagram F e }

