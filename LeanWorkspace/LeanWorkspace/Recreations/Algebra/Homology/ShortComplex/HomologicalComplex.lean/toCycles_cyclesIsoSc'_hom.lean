import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem toCycles_cyclesIsoSc'_hom :
    K.toCycles i j ≫ (K.cyclesIsoSc' i j k hi hk).hom = (K.sc' i j k).toCycles := by
  simp only [← cancel_mono (K.sc' i j k).iCycles, assoc, HomologicalComplex.cyclesIsoSc'_hom_iCycles,
    HomologicalComplex.toCycles_i, ShortComplex.toCycles_i, shortComplexFunctor'_obj_f]

