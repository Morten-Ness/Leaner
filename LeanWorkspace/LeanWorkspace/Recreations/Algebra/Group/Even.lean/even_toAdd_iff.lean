import Mathlib

variable {F α β : Type*}

variable [Add α]

theorem even_toAdd_iff {a : Multiplicative α} : Even a.toAdd ↔ IsSquare a := Iff.rfl

