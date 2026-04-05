import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

variable {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
  [K.HasHomology i] [L.HasHomology i]

theorem cyclesOpIso_inv_naturality :
    (opcyclesMap φ i).op ≫ (K.cyclesOpIso i).inv =
      (L.cyclesOpIso i).inv ≫ cyclesMap ((HomologicalComplex.opFunctor _ _).map φ.op) _ := ShortComplex.cyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

