import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem BoundaryLE.notMem {j : ι} (hj : e.BoundaryLE j) {k' : ι'} (hk' : c'.Rel (e.f j) k')
    (a : ι) : e.f a ≠ k' := fun ha =>
  hj.2 a (by simpa only [ha] using hk')

