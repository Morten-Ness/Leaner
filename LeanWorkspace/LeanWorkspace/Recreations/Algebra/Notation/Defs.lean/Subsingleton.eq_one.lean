import Mathlib

variable {G : Type*}

variable {α : Type u}

theorem Subsingleton.eq_one [One α] [Subsingleton α] (a : α) : a = 1 := Subsingleton.elim _ _

