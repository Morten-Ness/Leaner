import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem BoundaryGE.notMem {j : ι} (hj : e.BoundaryGE j) {i' : ι'} (hi' : c'.Rel i' (e.f j))
    (a : ι) : e.f a ≠ i' := fun ha =>
  hj.2 a (by simpa only [ha] using hi')

