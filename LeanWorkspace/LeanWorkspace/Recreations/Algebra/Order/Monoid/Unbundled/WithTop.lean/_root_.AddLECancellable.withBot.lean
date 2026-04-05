import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem _root_.AddLECancellable.withBot [LE α] (ha : AddLECancellable a) :
    AddLECancellable (a : WithBot α) := by
  rintro (_ | b) (_ | c)
  · simp [none_eq_bot]
  · simp [none_eq_bot]
  · simp [some_eq_coe, ← coe_add, none_eq_bot]
  · simpa [none_eq_bot, some_eq_coe, ← coe_add] using fun a ↦ ha a

