import Mathlib

variable {α : Type*}

variable [Lattice α] [Group α]

variable [MulLeftMono α] [MulRightMono α]

theorem div_inf (a b c : α) : c / (a ⊓ b) = c / a ⊔ c / b := (OrderIso.divLeft c).map_inf _ _

-- In fact 0 ≤ n•a implies 0 ≤ a, see L. Fuchs, "Partially ordered algebraic systems"
-- Chapter V, 1.E
-- See also `one_le_pow_iff` for the existing version in linear orders

