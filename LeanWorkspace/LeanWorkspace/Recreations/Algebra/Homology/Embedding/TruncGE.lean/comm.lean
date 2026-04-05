import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

set_option backward.isDefEq.respectTransparency false in
theorem comm (i j : ι) :
    HomologicalComplex.restrictionToTruncGE'.f K e i ≫ (K.truncGE' e).d i j = (K.restriction e).d i j ≫ HomologicalComplex.restrictionToTruncGE'.f K e j := by
  by_cases hij : c.Rel i j
  · by_cases hi : e.BoundaryGE i
    · rw [HomologicalComplex.restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv K e rfl hi,
        HomologicalComplex.restrictionToTruncGE'.f_eq_iso_hom_iso_inv K e rfl (e.not_boundaryGE_next hij),
        K.truncGE'_d_eq_fromOpcycles e hij rfl rfl hi]
      simp [restrictionXIso]
    · rw [HomologicalComplex.restrictionToTruncGE'.f_eq_iso_hom_iso_inv K e rfl hi,
        HomologicalComplex.restrictionToTruncGE'.f_eq_iso_hom_iso_inv K e rfl (e.not_boundaryGE_next hij),
        K.truncGE'_d_eq e hij rfl rfl hi]
      simp [restrictionXIso]
  · simp [HomologicalComplex.shape _ _ _ hij]

