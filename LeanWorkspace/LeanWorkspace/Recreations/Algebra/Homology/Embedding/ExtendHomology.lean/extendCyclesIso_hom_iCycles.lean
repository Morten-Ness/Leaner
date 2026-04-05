import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

set_option backward.isDefEq.respectTransparency false in
theorem extendCyclesIso_hom_iCycles :
    (K.extendCyclesIso e hj').hom ≫ K.iCycles j =
      (K.extend e).iCycles j' ≫ (K.extendXIso e hj').hom := by
  rw [← cancel_epi (K.extendCyclesIso e hj').inv, Iso.inv_hom_id_assoc]
  dsimp [HomologicalComplex.extendCyclesIso, iCycles]
  rw [assoc, ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles_assoc]
  dsimp
  rw [assoc, Iso.inv_hom_id, comp_id,
    ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]

