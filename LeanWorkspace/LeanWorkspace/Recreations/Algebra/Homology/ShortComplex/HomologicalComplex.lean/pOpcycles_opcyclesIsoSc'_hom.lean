import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem pOpcycles_opcyclesIsoSc'_hom :
    K.pOpcycles j ≫ (K.opcyclesIsoSc' i j k hi hk).hom = (K.sc' i j k).pOpcycles := by
  simp [HomologicalComplex.opcyclesIsoSc', HomologicalComplex.pOpcycles]

