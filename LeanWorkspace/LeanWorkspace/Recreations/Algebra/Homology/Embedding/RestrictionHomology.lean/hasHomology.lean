import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')

include hi hk hi' hj' hk' hi'' hk'' in
theorem hasHomology [K.HasHomology j'] : (K.restriction e).HasHomology j := ShortComplex.hasHomology_of_iso (K.isoSc' i' j' k' hi'' hk'' ≪≫
    (HomologicalComplex.restriction.sc'Iso K e i j k hi' hj' hk' hi'' hk'').symm ≪≫
    ((K.restriction e).isoSc' i j k hi hk).symm)

