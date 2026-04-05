import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.apply {A : Matrix n n α} (h : A.IsSymm) (i j : n) : A j i = A i j := Matrix.IsSymm.ext_iff.1 h i j

