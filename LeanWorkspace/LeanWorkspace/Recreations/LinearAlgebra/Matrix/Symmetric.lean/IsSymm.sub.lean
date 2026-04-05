import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.sub {A B : Matrix n n α} [Sub α] (hA : A.IsSymm) (hB : B.IsSymm) : (A - B).IsSymm := (transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

