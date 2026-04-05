import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem BoundaryGE.false_of_isTruncLE {j : ι} (hj : e.BoundaryGE j) [e.IsTruncLE] : False := by
  obtain ⟨i, hi⟩ := e.mem_prev hj.1
  exact hj.2 i (by simpa only [hi] using hj.1)

