import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

variable {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
  [K.HasHomology i] [L.HasHomology i]

theorem opcyclesOpIso_inv_naturality :
    (cyclesMap φ i).op ≫ (K.opcyclesOpIso i).inv =
      (L.opcyclesOpIso i).inv ≫ opcyclesMap ((HomologicalComplex.opFunctor _ _).map φ.op) _ := ShortComplex.opcyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

