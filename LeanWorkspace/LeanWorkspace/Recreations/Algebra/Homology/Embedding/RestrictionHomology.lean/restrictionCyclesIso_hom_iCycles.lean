import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
  [K.HasHomology j'] [(K.restriction e).HasHomology j]

theorem restrictionCyclesIso_hom_iCycles :
    (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫ K.iCycles j' =
      (K.restriction e).iCycles j ≫ (K.restrictionXIso e hj').hom := by
  simp [HomologicalComplex.restrictionCyclesIso]

