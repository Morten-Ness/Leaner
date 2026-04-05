import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [CommGroup α] [MulLeftMono α]

variable (s t : Interval α)

theorem bot_div : ⊥ / t = ⊥ := WithBot.map₂_bot_left _ _

