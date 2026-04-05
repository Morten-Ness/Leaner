import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable [CategoryWithHomology C]

theorem shiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    (CochainComplex.ShiftSequence.shiftIso C n a a' ha').hom.app K =
      ShortComplex.homologyMap ((CochainComplex.shiftShortComplexFunctorIso C n a a' ha').hom.app K) := by
  simp [CochainComplex.ShiftSequence.shiftIso, HomologicalComplex.homology]

