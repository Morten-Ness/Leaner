import Mathlib

variable {α : Type*}

variable [Lattice α] [Group α]

theorem mul_inf [MulLeftMono α] (a b c : α) :
    c * (a ⊓ b) = c * a ⊓ c * b := (OrderIso.mulLeft _).map_inf _ _

