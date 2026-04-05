import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem pOpcycles_opcyclesIsoSc'_inv :
    (K.sc' i j k).pOpcycles ≫ (K.opcyclesIsoSc' i j k hi hk).inv = K.pOpcycles j := by
  dsimp [HomologicalComplex.opcyclesIsoSc']
  simp only [ShortComplex.p_opcyclesMap, shortComplexFunctor'_obj_X₂, shortComplexFunctor_obj_X₂,
    natIsoSc'_inv_app_τ₂, id_comp]
  rfl

