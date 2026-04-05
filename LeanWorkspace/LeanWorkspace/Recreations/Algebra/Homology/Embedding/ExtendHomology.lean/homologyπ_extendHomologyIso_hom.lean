import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

set_option backward.isDefEq.respectTransparency false in
theorem homologyπ_extendHomologyIso_hom :
    (K.extend e).homologyπ j' ≫ (K.extendHomologyIso e hj').hom =
      (K.extendCyclesIso e hj').hom ≫ K.homologyπ j := by
  dsimp [HomologicalComplex.extendHomologyIso, homologyπ]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
    ← cancel_mono (K.sc j).homologyData.left.homologyIso.hom,
    assoc, assoc, assoc, Iso.inv_hom_id, comp_id,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  dsimp [HomologicalComplex.extendCyclesIso]
  simp only [assoc, Iso.inv_hom_id_assoc]

