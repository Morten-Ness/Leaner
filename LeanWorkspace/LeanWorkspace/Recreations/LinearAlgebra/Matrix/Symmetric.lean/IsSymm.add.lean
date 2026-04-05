import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.add {A B : Matrix n n α} [Add α] (hA : A.IsSymm) (hB : B.IsSymm) : (A + B).IsSymm := (transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

