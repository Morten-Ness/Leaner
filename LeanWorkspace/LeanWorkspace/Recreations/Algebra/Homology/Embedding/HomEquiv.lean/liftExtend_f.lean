import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

variable (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ)

variable {i' : ι'} {i : ι} (hi : e.f i = i')

theorem liftExtend_f :
    (e.liftExtend φ hφ).f i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫
      (L.extendXIso e hi).inv := by
  apply ComplexShape.Embedding.liftExtend.f_eq ComplexShape.Embedding.liftExtend

