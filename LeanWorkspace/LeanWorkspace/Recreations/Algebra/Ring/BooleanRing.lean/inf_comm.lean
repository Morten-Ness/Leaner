import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a := by
  dsimp only [(· ⊓ ·)]
  ring

