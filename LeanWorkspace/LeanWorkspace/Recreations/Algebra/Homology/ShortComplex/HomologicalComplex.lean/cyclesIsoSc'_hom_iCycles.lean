import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem cyclesIsoSc'_hom_iCycles :
    (K.cyclesIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).iCycles = K.iCycles j := by
  dsimp [HomologicalComplex.cyclesIsoSc']
  simp only [ShortComplex.cyclesMap_i, shortComplexFunctor_obj_X₂, shortComplexFunctor'_obj_X₂,
    natIsoSc'_hom_app_τ₂, comp_id]
  rfl

