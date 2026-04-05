import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [IdemSemiring α] {a b c : α}

theorem add_le (ha : a ≤ c) (hb : b ≤ c) : a + b ≤ c := add_le_iff.2 ⟨ha, hb⟩

-- See note [lower instance priority]

