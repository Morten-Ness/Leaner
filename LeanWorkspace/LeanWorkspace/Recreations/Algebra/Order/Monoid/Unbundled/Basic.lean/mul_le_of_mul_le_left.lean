import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_le_of_mul_le_left [MulLeftMono α] {a b c d : α} (h : a * b ≤ c)
    (hle : d ≤ b) :
    a * d ≤ c := @act_rel_of_rel_of_act_rel _ _ _ (· ≤ ·) _ _ a _ _ _ hle h

