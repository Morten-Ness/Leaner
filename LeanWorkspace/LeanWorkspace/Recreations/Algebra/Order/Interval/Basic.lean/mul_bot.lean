import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [Mul α] [MulLeftMono α] [MulRightMono α]

variable (s t : Interval α)

theorem mul_bot : s * ⊥ = ⊥ := WithBot.map₂_bot_right _ _

-- simp can already prove `add_bot`
attribute [simp] mul_bot

