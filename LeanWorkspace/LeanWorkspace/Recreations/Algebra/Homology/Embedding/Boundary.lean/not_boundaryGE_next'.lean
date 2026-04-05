import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem not_boundaryGE_next' [e.IsRelIff] {j k : ι} (hj : ¬ e.BoundaryGE j) (hk : c.next j = k) :
    ¬ e.BoundaryGE k := by
  by_cases hjk : c.Rel j k
  · exact ComplexShape.Embedding.not_boundaryGE_next e hjk
  · subst hk
    simpa only [c.next_eq_self j hjk] using hj

