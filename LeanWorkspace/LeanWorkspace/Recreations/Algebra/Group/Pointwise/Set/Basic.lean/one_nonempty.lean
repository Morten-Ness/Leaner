import Mathlib

variable {F α β γ : Type*}

variable [One α] {s : Set α} {a : α}

theorem one_nonempty : (1 : Set α).Nonempty := ⟨1, rfl⟩

