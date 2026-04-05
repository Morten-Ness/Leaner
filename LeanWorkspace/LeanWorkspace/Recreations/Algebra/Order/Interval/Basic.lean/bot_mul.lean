import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [Mul α] [MulLeftMono α] [MulRightMono α]

variable (s t : Interval α)

theorem bot_mul : ⊥ * t = ⊥ := WithBot.map₂_bot_left _ _

