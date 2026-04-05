import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

theorem add_left_injective_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ x + b) := (IsAddRegular.of_ne_top h).2

