import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

theorem quasiIso_unopFunctor_map_iff
    {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso ((HomologicalComplex.unopFunctor _ _).map φ.op) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, HomologicalComplex.quasiIsoAt_unopFunctor_map_iff]

