import Mathlib

variable {α : Type u}

variable [Mul α]

variable [LE α] [CanonicallyOrderedMul α] {a b c : α}

theorem le_iff_exists_mul : a ≤ b ↔ ∃ c, b = a * c := ⟨exists_mul_of_le, by
    rintro ⟨c, rfl⟩
    exact le_self_mul⟩

