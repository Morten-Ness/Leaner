import Mathlib

variable {F α β γ : Type*}

variable [One α] {s : Set α} {a : α}

theorem one_mem_one : (1 : α) ∈ (1 : Set α) := Eq.refl _

