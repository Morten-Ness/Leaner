import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem restrictionToTruncGE'_hasLift : e.HasLift (K.restrictionToTruncGE' e) := by
  intro j hj i' _
  dsimp [HomologicalComplex.restrictionToTruncGE']
  rw [HomologicalComplex.restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv HomologicalComplex.restrictionToTruncGE' K e rfl hj]
  simp [restrictionXIso]

