import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_apply (i : n) : Matrix.cramer A b i = (A.updateCol i b).det := rfl

