import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

theorem add_left_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono (fun x ↦ x + b) := add_left_mono.strictMono_of_injective <| add_left_injective_of_ne_top _ h

