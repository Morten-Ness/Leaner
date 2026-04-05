import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem truncLE'ToRestriction_naturality :
    HomologicalComplex.truncLE'Map φ e ≫ L.truncLE'ToRestriction e =
      K.truncLE'ToRestriction e ≫ restrictionMap φ e := (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (restrictionToTruncGE'_naturality ((opFunctor C c').map φ.op) e.op))

