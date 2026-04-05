import Mathlib

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (e : Embedding c c')

theorem mem_prev [e.IsTruncLE] {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) : ∃ i, e.f i = i' := IsTruncLE.mem_prev h

