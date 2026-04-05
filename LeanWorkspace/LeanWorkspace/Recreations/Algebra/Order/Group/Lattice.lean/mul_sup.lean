import Mathlib

variable {α : Type*}

variable [Lattice α] [Group α]

theorem mul_sup [MulLeftMono α] (a b c : α) :
    c * (a ⊔ b) = c * a ⊔ c * b := (OrderIso.mulLeft _).map_sup _ _

