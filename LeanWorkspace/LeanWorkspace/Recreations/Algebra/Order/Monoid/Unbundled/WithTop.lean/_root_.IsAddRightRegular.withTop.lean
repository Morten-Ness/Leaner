import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem _root_.IsAddRightRegular.withTop (ha : IsAddRightRegular a) :
    IsAddRightRegular (a : WithTop α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

