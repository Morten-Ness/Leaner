import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)

variable {j' : ι'} (hj' : e.f j = j') (hj : e.BoundaryGE j)

theorem homologyData_right_g' :
    (HomologicalComplex.truncGE'.homologyData K e i j k hk hj' hj).right.g' = (K.truncGE' e).d j k := rfl

