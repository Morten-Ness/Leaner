import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

theorem homRestrict_precomp (α : K' ⟶ K) (ψ : K ⟶ L.extend e) :
    e.homRestrict (α ≫ ψ) = restrictionMap α e ≫ e.homRestrict ψ := by
  ext i
  simp [ComplexShape.Embedding.homRestrict_f _ _ rfl, restrictionXIso]

