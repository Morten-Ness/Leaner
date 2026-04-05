import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem _root_.AddLECancellable.withTop [LE α] (ha : AddLECancellable a) :
    AddLECancellable (a : WithTop α) := by
  rintro (_ | b) (_ | c)
  · simp [none_eq_top]
  · simp [none_eq_top]
  · simp [some_eq_coe, ← coe_add, none_eq_top]
  · simpa [none_eq_top, some_eq_coe, ← coe_add] using fun a ↦ ha a

