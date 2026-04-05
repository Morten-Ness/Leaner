import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

theorem π_homologyIsoSc'_hom :
    K.homologyπ j ≫ (K.homologyIsoSc' i j k hi hk).hom =
      (K.cyclesIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).homologyπ := by
  apply ShortComplex.homologyπ_naturality

