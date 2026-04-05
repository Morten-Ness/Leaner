import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem le_mul_of_le_mul_left [MulLeftMono α] {a b c d : α} (h : a ≤ b * c)
    (hle : c ≤ d) :
    a ≤ b * d := @rel_act_of_rel_of_rel_act _ _ _ (· ≤ ·) _ _ b _ _ _ hle h

