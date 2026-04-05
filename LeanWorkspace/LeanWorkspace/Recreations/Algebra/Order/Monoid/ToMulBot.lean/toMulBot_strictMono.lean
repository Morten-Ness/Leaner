import Mathlib

variable {α : Type u}

variable [Add α]

variable [Preorder α] (a b : WithZero (Multiplicative α))

theorem toMulBot_strictMono : StrictMono (@WithZero.toMulBot α _) := fun _ _ => id

