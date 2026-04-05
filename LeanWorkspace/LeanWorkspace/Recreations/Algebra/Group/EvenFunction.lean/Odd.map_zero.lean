import Mathlib

variable {α β : Type*} [Neg α]

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

theorem Odd.map_zero [NegZeroClass α] (hf : f.Odd) : f 0 = 0 := by simp [← neg_eq_self, ← hf 0]

