import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [CommGroup α] [MulLeftMono α]

variable (s t : Interval α)

theorem div_bot : s / ⊥ = ⊥ := WithBot.map₂_bot_right _ _

