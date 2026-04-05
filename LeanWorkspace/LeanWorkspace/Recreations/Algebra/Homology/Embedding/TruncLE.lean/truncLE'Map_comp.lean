import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem truncLE'Map_comp : HomologicalComplex.truncLE'Map (φ ≫ φ') e = HomologicalComplex.truncLE'Map φ e ≫ HomologicalComplex.truncLE'Map φ' e := (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGE'Map_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))

