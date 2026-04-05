import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
  [K.HasHomology j'] [(K.restriction e).HasHomology j]

set_option backward.isDefEq.respectTransparency false in
theorem pOpcycles_restrictionOpcyclesIso_hom :
    (K.restriction e).pOpcycles j ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom =
      (K.restrictionXIso e hj').hom ≫ K.pOpcycles j' := by
  simp [HomologicalComplex.restrictionOpcyclesIso]

