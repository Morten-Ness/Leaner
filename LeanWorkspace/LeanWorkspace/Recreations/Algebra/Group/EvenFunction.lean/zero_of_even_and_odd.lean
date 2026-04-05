import Mathlib

variable {α β : Type*} [Neg α]

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

theorem zero_of_even_and_odd [Neg α] (he : f.Even) (ho : f.Odd) : f = 0 := by
  ext r
  rw [Pi.zero_apply, ← neg_eq_self, ← ho, he]

