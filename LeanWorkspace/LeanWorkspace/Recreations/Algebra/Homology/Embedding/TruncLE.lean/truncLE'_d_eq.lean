import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem truncLE'_d_eq {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hj : ¬ e.BoundaryLE j) :
    (K.truncLE' e).d i j = (K.truncLE'XIso e hi' (e.not_boundaryLE_prev hij)).hom ≫ K.d i' j' ≫
        (K.truncLE'XIso e hj' hj).inv := Quiver.Hom.op_inj (by simpa using K.op.truncGE'_d_eq e.op hij hj' hi' (by simpa))

