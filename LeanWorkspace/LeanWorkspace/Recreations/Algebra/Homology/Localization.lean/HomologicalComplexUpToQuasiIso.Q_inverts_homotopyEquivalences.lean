import Mathlib

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

theorem HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences
    [(HomologicalComplex.quasiIso C c).HasLocalization] :
    (HomologicalComplex.homotopyEquivalences C c).IsInvertedBy
      HomologicalComplexUpToQuasiIso.Q := MorphismProperty.IsInvertedBy.of_le _ _ _
    (Localization.inverts Q (HomologicalComplex.quasiIso C c))
    (homotopyEquivalences_le_quasiIso C c)

