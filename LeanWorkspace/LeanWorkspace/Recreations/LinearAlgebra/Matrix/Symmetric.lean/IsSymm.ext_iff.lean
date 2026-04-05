import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.ext_iff {A : Matrix n n α} : A.IsSymm ↔ ∀ i j, A j i = A i j := Matrix.ext_iff.symm

