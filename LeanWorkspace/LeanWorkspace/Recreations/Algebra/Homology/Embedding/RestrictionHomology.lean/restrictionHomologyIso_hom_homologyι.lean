import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
  [K.HasHomology j'] [(K.restriction e).HasHomology j]

theorem restrictionHomologyIso_hom_homologyι :
    (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom ≫ K.homologyι j' =
      (K.restriction e).homologyι j ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom := by
  rw [← cancel_epi (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv,
    Iso.inv_hom_id_assoc, restrictionHomologyIso_inv_homologyι_assoc,
      Iso.inv_hom_id, comp_id]

