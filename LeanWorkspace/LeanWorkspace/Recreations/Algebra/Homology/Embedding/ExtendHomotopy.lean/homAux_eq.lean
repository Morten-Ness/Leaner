import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

variable (e : c.Embedding c') (φ : ∀ i j, K.X i ⟶ L.X j)

theorem homAux_eq (i' j' : Option ι) (i j : ι) (hi : i' = some i) (hj : j' = some j) :
    Homotopy.extend.homAux φ i' j' = (Homotopy.extend.XIso K hi).hom ≫ φ i j ≫ (Homotopy.extend.XIso L hj).inv := by
  subst hi hj
  simp [Homotopy.extend.homAux, Homotopy.extend.XIso, Homotopy.extend.X]

