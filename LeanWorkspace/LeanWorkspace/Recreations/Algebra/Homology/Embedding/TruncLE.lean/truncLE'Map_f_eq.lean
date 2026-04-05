import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem truncLE'Map_f_eq {i : ι} (hi : ¬ e.BoundaryLE i) {i' : ι'} (h : e.f i = i') :
    (HomologicalComplex.truncLE'Map φ e).f i =
      (K.truncLE'XIso e h hi).hom ≫ φ.f i' ≫ (L.truncLE'XIso e h hi).inv := Quiver.Hom.op_inj
    (by simpa using truncGE'Map_f_eq ((opFunctor C c').map φ.op) e.op (by simpa) h)

