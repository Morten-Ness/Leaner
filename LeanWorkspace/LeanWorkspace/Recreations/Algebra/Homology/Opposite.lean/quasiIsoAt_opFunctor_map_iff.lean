import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

theorem quasiIsoAt_opFunctor_map_iff
    {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt ((HomologicalComplex.opFunctor _ _).map φ.op) i ↔ QuasiIsoAt φ i := by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_opMap_iff ((shortComplexFunctor V c i).map φ)

