import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem _root_.IsAddRightRegular.withBot (ha : IsAddRightRegular a) :
    IsAddRightRegular (a : WithBot α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

