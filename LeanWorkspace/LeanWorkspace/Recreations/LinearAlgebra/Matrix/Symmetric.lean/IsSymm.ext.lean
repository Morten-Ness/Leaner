import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.ext {A : Matrix n n α} : (∀ i j, A j i = A i j) → A.IsSymm := Matrix.ext

