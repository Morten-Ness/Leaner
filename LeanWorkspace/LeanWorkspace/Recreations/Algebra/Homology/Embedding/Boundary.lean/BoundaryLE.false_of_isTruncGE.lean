import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem BoundaryLE.false_of_isTruncGE {j : ι} (hj : e.BoundaryLE j) [e.IsTruncGE] : False := by
  obtain ⟨k, hk⟩ := e.mem_next hj.1
  exact hj.2 k (by simpa only [hk] using hj.1)

