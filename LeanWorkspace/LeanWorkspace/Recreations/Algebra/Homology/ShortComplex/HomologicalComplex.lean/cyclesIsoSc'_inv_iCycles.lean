import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem cyclesIsoSc'_inv_iCycles :
    (K.cyclesIsoSc' i j k hi hk).inv ≫ K.iCycles j = (K.sc' i j k).iCycles := by
  simp [HomologicalComplex.cyclesIsoSc', HomologicalComplex.iCycles]

