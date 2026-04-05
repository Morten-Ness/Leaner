import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

theorem homRestrict_comp_extendMap (ψ : K ⟶ L.extend e) (β : L ⟶ L') :
    e.homRestrict (ψ ≫ extendMap β e) =
      e.homRestrict ψ ≫ β := by
  ext i
  simp [ComplexShape.Embedding.homRestrict_f _ _ rfl, extendMap_f β e rfl]

