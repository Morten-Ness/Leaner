import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

theorem homology_sc'_eq_homology [(K.sc' (c.prev j) j (c.next j)).HasHomology] :
    (K.sc' (c.prev j) j (c.next j)).homology = K.homology j := rfl

