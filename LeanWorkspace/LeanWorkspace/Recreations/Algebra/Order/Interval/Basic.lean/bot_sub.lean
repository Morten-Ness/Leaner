import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] [AddLeftMono α]

variable (s t : Interval α)

theorem bot_sub : ⊥ - t = ⊥ := WithBot.map₂_bot_left _ _

