import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

variable (ψ : K ⟶ L.extend e)

theorem f_eq {i : ι} {i' : ι'} (h : e.f i = i') :
    ComplexShape.Embedding.homRestrict.f ψ i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom := by
  subst h
  simp [ComplexShape.Embedding.homRestrict.f, restrictionXIso]

