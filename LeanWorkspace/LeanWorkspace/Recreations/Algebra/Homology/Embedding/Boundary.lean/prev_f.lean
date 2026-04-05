import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem prev_f [e.IsTruncLE] {i j : ι} (hij : c.prev j = i) : c'.prev (e.f j) = e.f i := ComplexShape.Embedding.next_f e.op hij

