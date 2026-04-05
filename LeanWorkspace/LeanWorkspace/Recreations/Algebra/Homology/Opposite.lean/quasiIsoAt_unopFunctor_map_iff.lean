import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

theorem quasiIsoAt_unopFunctor_map_iff
    {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt ((HomologicalComplex.unopFunctor _ _).map φ.op) i ↔ QuasiIsoAt φ i := by
  rw [← HomologicalComplex.quasiIsoAt_opFunctor_map_iff]
  rfl

