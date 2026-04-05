import Mathlib

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (e : Embedding c c')

theorem mem_next [e.IsTruncGE] {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') : ∃ k, e.f k = k' := IsTruncGE.mem_next h

