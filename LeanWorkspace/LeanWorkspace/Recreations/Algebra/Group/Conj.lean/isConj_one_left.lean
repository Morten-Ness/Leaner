import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem isConj_one_left {a : α} : IsConj a 1 ↔ a = 1 := calc
    IsConj a 1 ↔ IsConj 1 a := ⟨IsConj.symm, IsConj.symm⟩
    _ ↔ a = 1 := isConj_one_right

