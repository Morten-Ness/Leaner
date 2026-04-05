import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

variable {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
  [K.HasHomology i] [L.HasHomology i]

theorem homologyOp_hom_naturality :
    homologyMap ((HomologicalComplex.opFunctor _ _).map φ.op) _ ≫ (K.homologyOp i).hom =
      (L.homologyOp i).hom ≫ (homologyMap φ i).op := ShortComplex.homologyOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

