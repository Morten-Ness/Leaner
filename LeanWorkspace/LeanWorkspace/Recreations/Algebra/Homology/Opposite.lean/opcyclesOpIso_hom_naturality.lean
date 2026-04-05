import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

variable {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
  [K.HasHomology i] [L.HasHomology i]

theorem opcyclesOpIso_hom_naturality :
    opcyclesMap ((HomologicalComplex.opFunctor _ _).map φ.op) _ ≫ (K.opcyclesOpIso i).hom =
      (L.opcyclesOpIso i).hom ≫ (cyclesMap φ i).op := ShortComplex.opcyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

set_option backward.isDefEq.respectTransparency false in -- This is needed in Algebra/Homology/Embedding/TruncLE.lean

