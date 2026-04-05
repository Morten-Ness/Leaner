import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem restrictionToTruncGE'_naturality :
    K.restrictionToTruncGE' e ≫ HomologicalComplex.truncGE'Map φ e =
      restrictionMap φ e ≫ L.restrictionToTruncGE' e := by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv _ e rfl hi,
      HomologicalComplex.truncGE'Map_f_eq_opcyclesMap φ e hi rfl, restrictionXIso]
  · simp [HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ e rfl hi,
      HomologicalComplex.truncGE'Map_f_eq φ e hi rfl, restrictionXIso]

attribute [local instance] epi_comp in

