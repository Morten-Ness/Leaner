import Mathlib

variable {α β : Type*}

theorem mulLECancellable_one [MulOneClass α] [LE α] : MulLECancellable (1 : α) := fun a b => by
  simpa only [one_mul] using id

