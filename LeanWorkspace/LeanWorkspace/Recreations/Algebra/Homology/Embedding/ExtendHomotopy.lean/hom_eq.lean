import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

variable (e : c.Embedding c') (φ : ∀ i j, K.X i ⟶ L.X j)

theorem hom_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    Homotopy.extend.hom e φ i' j' = (K.extendXIso e hi).hom ≫ φ i j ≫ (L.extendXIso e hj).inv := Homotopy.extend.homAux_eq φ (e.r i') (e.r j') i j (e.r_eq_some hi) (e.r_eq_some hj)

