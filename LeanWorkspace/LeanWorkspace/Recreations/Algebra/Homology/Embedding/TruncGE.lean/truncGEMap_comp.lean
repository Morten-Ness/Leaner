import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

variable [HasZeroObject C]

theorem truncGEMap_comp : HomologicalComplex.truncGEMap (φ ≫ φ') e = HomologicalComplex.truncGEMap φ e ≫ HomologicalComplex.truncGEMap φ' e := by
  simp [HomologicalComplex.truncGEMap, HomologicalComplex.truncGE]

