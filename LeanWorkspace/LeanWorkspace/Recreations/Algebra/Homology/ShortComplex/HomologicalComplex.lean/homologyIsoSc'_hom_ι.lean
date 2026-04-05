import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

theorem homologyIsoSc'_hom_ι :
    (K.homologyIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).homologyι =
      K.homologyι j ≫ (K.opcyclesIsoSc' i j k hi hk).hom := by
  apply ShortComplex.homologyι_naturality

