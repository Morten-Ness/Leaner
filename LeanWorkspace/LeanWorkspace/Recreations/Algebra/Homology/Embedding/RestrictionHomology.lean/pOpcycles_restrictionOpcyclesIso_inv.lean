import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
  [K.HasHomology j'] [(K.restriction e).HasHomology j]

theorem pOpcycles_restrictionOpcyclesIso_inv :
    K.pOpcycles j' ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').inv =
      (K.restrictionXIso e hj').inv ≫ (K.restriction e).pOpcycles j := by
  simp [HomologicalComplex.restrictionOpcyclesIso]

