import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

theorem extend_hom_eq (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff]
    {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    (h.extend e).hom i' j' = (K.extendXIso e hi).hom ≫ h.hom i j ≫ (L.extendXIso e hj).inv := Homotopy.extend.hom_eq Homotopy.extend _ _ _ _

