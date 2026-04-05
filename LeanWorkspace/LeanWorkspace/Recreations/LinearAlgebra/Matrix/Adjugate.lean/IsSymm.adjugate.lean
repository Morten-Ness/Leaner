import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem IsSymm.adjugate {A : Matrix n n α} (hA : A.IsSymm) : A.adjugate.IsSymm := by
  rw [Matrix.IsSymm, Matrix.adjugate_transpose, hA.eq]
