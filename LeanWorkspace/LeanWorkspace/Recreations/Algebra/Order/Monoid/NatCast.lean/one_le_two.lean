import Mathlib

variable {α : Type*}

variable [AddMonoidWithOne α]

theorem one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] :
    (1 : α) ≤ 2 := calc (1 : α) = 1 + 0 := (add_zero 1).symm
     _ ≤ 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two

