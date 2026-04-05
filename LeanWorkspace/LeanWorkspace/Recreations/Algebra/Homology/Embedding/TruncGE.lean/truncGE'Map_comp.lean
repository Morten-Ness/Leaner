import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem truncGE'Map_comp : HomologicalComplex.truncGE'Map (φ ≫ φ') e = HomologicalComplex.truncGE'Map φ e ≫ HomologicalComplex.truncGE'Map φ' e := by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [HomologicalComplex.truncGE'Map_f_eq_opcyclesMap _ _ hi rfl, opcyclesMap_comp]
  · simp [HomologicalComplex.truncGE'Map_f_eq _ _ hi rfl]

