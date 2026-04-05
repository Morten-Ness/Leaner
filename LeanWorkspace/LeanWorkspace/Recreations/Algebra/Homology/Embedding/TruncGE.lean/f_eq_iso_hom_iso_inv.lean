import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem f_eq_iso_hom_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    HomologicalComplex.restrictionToTruncGE'.f K e i = (K.restrictionXIso e hi').hom ≫ (K.truncGE'XIso e hi' hi).inv := by
  dsimp [HomologicalComplex.restrictionToTruncGE'.f]
  rw [dif_neg hi]
  subst hi'
  simp [restrictionXIso]

