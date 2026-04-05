import Mathlib

variable {α : Type*}

theorem tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub α] {a b c : α} :
    a - b ≤ c ↔ a ≤ c + b := OrderedSub.tsub_le_iff_right a b c

