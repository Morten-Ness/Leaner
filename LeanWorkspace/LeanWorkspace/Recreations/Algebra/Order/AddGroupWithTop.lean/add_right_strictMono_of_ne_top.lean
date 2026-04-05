import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

theorem add_right_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono (fun x ↦ b + x) := add_right_mono.strictMono_of_injective <| add_right_injective_of_ne_top _ h

