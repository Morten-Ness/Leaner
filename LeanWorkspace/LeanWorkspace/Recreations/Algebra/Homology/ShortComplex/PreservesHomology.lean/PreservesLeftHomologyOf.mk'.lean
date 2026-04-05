import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable (F : C ⥤ D) [PreservesZeroMorphisms F] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

theorem PreservesLeftHomologyOf.mk' (h : S.LeftHomologyData) [h.IsPreservedBy F] :
    F.PreservesLeftHomologyOf S where
  isPreservedBy h' := { g := ShortComplex.LeftHomologyData.IsPreservedBy.hg h F
      f' := by
        have := ShortComplex.LeftHomologyData.IsPreservedBy.hf' h F
        let e : parallelPair h.f' 0 ≅ parallelPair h'.f' 0 :=
          parallelPair.ext (Iso.refl _) (ShortComplex.cyclesMapIso' (Iso.refl S) h h')
            (by simp) (by simp)
        exact preservesColimit_of_iso_diagram F e }

