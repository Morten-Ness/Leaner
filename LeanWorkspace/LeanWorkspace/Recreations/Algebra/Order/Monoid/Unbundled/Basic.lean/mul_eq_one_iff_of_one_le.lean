import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [PartialOrder α]

theorem mul_eq_one_iff_of_one_le [MulLeftMono α]
    [MulRightMono α] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * b = 1 ↔ a = 1 ∧ b = 1 := Iff.intro
    (fun hab : a * b = 1 =>
      have : a ≤ 1 := hab ▸ le_mul_of_le_of_one_le le_rfl hb
      have : a = 1 := le_antisymm this ha
      have : b ≤ 1 := hab ▸ le_mul_of_one_le_of_le ha le_rfl
      have : b = 1 := le_antisymm this hb
      And.intro ‹a = 1› ‹b = 1›)
    (by rintro ⟨rfl, rfl⟩; rw [mul_one])

