import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

theorem restrictionMap_f' {i : ι} {i' : ι'} (hi : e.f i = i') :
    (HomologicalComplex.restrictionMap φ e).f i = (K.restrictionXIso e hi).hom ≫
      φ.f i' ≫ (L.restrictionXIso e hi).inv := by
  subst hi
  simp [HomologicalComplex.restrictionXIso]

