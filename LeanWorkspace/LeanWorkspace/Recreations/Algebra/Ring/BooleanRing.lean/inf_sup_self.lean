import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

theorem inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [mul_add, mul_add, BooleanRing.mul_self, ← mul_assoc, BooleanRing.mul_self, add_assoc, BooleanRing.add_self, add_zero]

