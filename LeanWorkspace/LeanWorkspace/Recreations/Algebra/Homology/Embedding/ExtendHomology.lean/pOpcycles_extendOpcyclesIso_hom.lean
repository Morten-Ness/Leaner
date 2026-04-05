import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

theorem pOpcycles_extendOpcyclesIso_hom :
    (K.extend e).pOpcycles j' ≫ (K.extendOpcyclesIso e hj').hom =
      (K.extendXIso e hj').hom ≫ K.pOpcycles j := by
  simp only [← cancel_mono (K.extendOpcyclesIso e hj').inv,
    assoc, Iso.hom_inv_id, comp_id, HomologicalComplex.pOpcycles_extendOpcyclesIso_inv, Iso.hom_inv_id_assoc]

