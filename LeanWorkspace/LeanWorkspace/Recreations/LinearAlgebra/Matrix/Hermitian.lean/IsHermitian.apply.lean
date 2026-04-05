import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem IsHermitian.apply {A : Matrix n n α} (h : A.IsHermitian) (i j : n) : star (A j i) = A i j := congr_fun (congr_fun h _) _

