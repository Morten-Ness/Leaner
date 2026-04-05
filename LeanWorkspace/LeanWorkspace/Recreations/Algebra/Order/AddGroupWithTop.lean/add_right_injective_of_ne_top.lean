import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

theorem add_right_injective_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ b + x) := (IsAddRegular.of_ne_top h).1

