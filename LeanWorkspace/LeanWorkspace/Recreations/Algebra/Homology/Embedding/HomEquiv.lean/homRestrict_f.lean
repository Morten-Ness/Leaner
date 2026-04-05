import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

theorem homRestrict_f (ψ : K ⟶ L.extend e) {i : ι} {i' : ι'} (h : e.f i = i') :
    (e.homRestrict ψ).f i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom := ComplexShape.Embedding.liftExtend.f_eq ComplexShape.Embedding.homRestrict ψ h

