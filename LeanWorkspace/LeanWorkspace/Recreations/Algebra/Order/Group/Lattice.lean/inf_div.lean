import Mathlib

variable {α : Type*}

variable [Lattice α] [Group α]

theorem inf_div [MulRightMono α] (a b c : α) :
    (a ⊓ b) / c = a / c ⊓ b / c := (OrderIso.divRight _).map_inf _ _

