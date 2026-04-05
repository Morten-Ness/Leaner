import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
  [K.HasHomology j'] [(K.restriction e).HasHomology j]

theorem homologyπ_restrictionHomologyIso_inv :
    K.homologyπ j' ≫ (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv =
      (K.restrictionCyclesIso e j k hk hj' hk' hk'').inv ≫ (K.restriction e).homologyπ j := by
  rw [← cancel_mono (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom,
    assoc, assoc, Iso.inv_hom_id, HomologicalComplex.homologyπ_restrictionHomologyIso_hom, comp_id,
    Iso.inv_hom_id_assoc]

