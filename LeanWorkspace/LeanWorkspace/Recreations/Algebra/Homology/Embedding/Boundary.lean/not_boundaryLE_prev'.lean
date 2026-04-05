import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem not_boundaryLE_prev' [e.IsRelIff] {i j : ι} (hj : ¬ e.BoundaryLE j) (hk : c.prev j = i) :
    ¬ e.BoundaryLE i := by
  by_cases hij : c.Rel i j
  · exact ComplexShape.Embedding.not_boundaryLE_prev e hij
  · subst hk
    simpa only [c.prev_eq_self j hij] using hj

