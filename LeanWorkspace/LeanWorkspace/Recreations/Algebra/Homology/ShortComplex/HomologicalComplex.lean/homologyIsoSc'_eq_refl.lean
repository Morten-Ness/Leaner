import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

theorem homologyIsoSc'_eq_refl
    [(K.sc' (c.prev j) j (c.next j)).HasHomology] :
    dsimp% K.homologyIsoSc' _ j _ rfl rfl = Iso.refl _ := by
  ext : 1
  apply ShortComplex.homologyMap_id

