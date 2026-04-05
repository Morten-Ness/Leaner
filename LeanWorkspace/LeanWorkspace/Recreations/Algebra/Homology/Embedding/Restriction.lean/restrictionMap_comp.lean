import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

theorem restrictionMap_comp :
    HomologicalComplex.restrictionMap (φ ≫ φ') e = HomologicalComplex.restrictionMap φ e ≫ HomologicalComplex.restrictionMap φ' e := rfl

