import Mathlib

variable {α β : Type*}

theorem mulLECancellable_mul [LE α] [CommSemigroup α] [MulLeftMono α] {a b : α} :
    MulLECancellable (a * b) ↔ MulLECancellable a ∧ MulLECancellable b := ⟨fun h ↦ ⟨h.of_mul_left, h.of_mul_right⟩, fun h ↦ h.1.mul h.2⟩

