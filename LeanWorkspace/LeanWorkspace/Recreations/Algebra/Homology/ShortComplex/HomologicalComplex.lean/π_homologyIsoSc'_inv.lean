import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

theorem π_homologyIsoSc'_inv :
    (K.sc' i j k).homologyπ ≫ (K.homologyIsoSc' i j k hi hk).inv =
      (K.cyclesIsoSc' i j k hi hk).inv ≫ K.homologyπ j := by
  apply ShortComplex.homologyπ_naturality

