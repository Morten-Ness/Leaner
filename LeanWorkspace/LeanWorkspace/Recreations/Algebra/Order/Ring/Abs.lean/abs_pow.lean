import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : ℕ} {a b : α}

theorem abs_pow (a : α) (n : ℕ) : |a ^ n| = |a| ^ n := (absHom.toMonoidHom : α →* α).map_pow _ _

