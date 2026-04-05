import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem d_eq {i j : Option ι} {a b : ι} (hi : i = some a) (hj : j = some b) :
    HomologicalComplex.extend.d K i j = (HomologicalComplex.extend.XIso K hi).hom ≫ K.d a b ≫ (HomologicalComplex.extend.XIso K hj).inv := by
  subst hi hj
  simp [HomologicalComplex.extend.XIso, HomologicalComplex.extend.X, HomologicalComplex.extend.d]

