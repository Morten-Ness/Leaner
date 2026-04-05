import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

variable {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
  [K.HasHomology i] [L.HasHomology i]

theorem cyclesOpIso_hom_naturality :
    cyclesMap ((HomologicalComplex.opFunctor _ _).map φ.op) _ ≫ (K.cyclesOpIso i).hom =
      (L.cyclesOpIso i).hom ≫ (opcyclesMap φ i).op := ShortComplex.cyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

