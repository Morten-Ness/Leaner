import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

theorem homRestrict_liftExtend (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ) :
    e.homRestrict (e.liftExtend φ hφ) = φ := by
  ext i
  simp [ComplexShape.Embedding.homRestrict_f e _ rfl, ComplexShape.Embedding.liftExtend_f e _ _ rfl]

