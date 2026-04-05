import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem IsSymm.inv {A : Matrix n n α} (hA : A.IsSymm) : A⁻¹.IsSymm := hA.adjugate.smul _

