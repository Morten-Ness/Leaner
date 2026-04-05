import Mathlib

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
  {ι : Type*} (c : ComplexShape ι)

variable [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  [(HomologicalComplex.quasiIso D c).HasLocalization]
  [F.Additive] [F.PreservesHomology]

theorem mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso :
    (HomologicalComplex.quasiIso C c).IsInvertedBy
      (F.mapHomologicalComplex c ⋙ HomologicalComplexUpToQuasiIso.Q) := by
  apply (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).inverts

