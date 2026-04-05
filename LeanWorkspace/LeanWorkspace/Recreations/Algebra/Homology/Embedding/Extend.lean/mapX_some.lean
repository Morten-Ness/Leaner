import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem mapX_some {i : Option ι} {a : ι} (hi : i = some a) :
    HomologicalComplex.extend.mapX φ i = (HomologicalComplex.extend.XIso K hi).hom ≫ φ.f a ≫ (HomologicalComplex.extend.XIso L hi).inv := by
  subst hi
  dsimp [HomologicalComplex.extend.XIso, HomologicalComplex.extend.X]
  rw [id_comp, comp_id]
  rfl

