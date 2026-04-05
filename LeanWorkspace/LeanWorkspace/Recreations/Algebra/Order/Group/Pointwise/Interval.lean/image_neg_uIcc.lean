import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem image_neg_uIcc : Neg.neg '' [[a, b]] = [[-a, -b]] := by simp

