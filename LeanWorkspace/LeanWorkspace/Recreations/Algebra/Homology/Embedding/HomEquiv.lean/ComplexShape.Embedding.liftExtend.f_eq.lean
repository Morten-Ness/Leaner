import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

variable (φ : K.restriction e ⟶ L)

theorem f_eq {i' : ι'} {i : ι} (hi : e.f i = i') :
    ComplexShape.Embedding.liftExtend.f φ i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).inv := by
  have hi' : ∃ k, e.f k = i' := ⟨i, hi⟩
  have : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  grind [ComplexShape.Embedding.liftExtend.f]

