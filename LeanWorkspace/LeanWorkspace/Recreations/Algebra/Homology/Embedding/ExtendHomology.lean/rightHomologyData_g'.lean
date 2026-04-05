import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')

set_option backward.isDefEq.respectTransparency false in
theorem rightHomologyData_g' (h : (K.sc' i j k).RightHomologyData) (hk'' : e.f k = k') :
    (HomologicalComplex.extend.rightHomologyData K e hj' hi hi' hk hk' h).g' = h.g' ≫ (K.extendXIso e hk'').inv := by
  rw [← cancel_epi h.p, ← cancel_epi (extendXIso K e hj').hom]
  have := (HomologicalComplex.extend.rightHomologyData K e hj' hi hi' hk hk' h).p_g'
  dsimp at this
  rw [assoc] at this
  rw [this, K.extend_d_eq e hj' hk'', h.p_g'_assoc, shortComplexFunctor'_obj_g]

