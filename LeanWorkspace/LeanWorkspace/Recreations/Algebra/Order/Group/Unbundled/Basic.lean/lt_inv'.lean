import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

variable [MulRightStrictMono α]

theorem lt_inv' : a < b⁻¹ ↔ b < a⁻¹ := by rw [← inv_lt_inv_iff, inv_inv]

alias ⟨lt_inv_of_lt_inv, _⟩ := lt_inv'

attribute [to_additive] lt_inv_of_lt_inv

alias ⟨inv_lt_of_inv_lt', _⟩ := inv_lt'

attribute [to_additive neg_lt_of_neg_lt] inv_lt_of_inv_lt'

