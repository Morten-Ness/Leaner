import Mathlib

variable {F α β γ : Type*}

variable [One α] {s : Set α} {a : α}

theorem mem_one : a ∈ (1 : Set α) ↔ a = 1 := Iff.rfl

