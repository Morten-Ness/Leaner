import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

theorem quasiIso_opFunctor_map_iff
    {K L : HomologicalComplex V c} (φ : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso ((HomologicalComplex.opFunctor _ _).map φ.op) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, HomologicalComplex.quasiIsoAt_opFunctor_map_iff]

