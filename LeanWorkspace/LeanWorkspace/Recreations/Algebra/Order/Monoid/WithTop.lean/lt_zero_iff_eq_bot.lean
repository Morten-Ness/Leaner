import Mathlib

variable {α : Type u}

theorem lt_zero_iff_eq_bot {α : Type*} [AddMonoid α] [Preorder α] [CanonicallyOrderedAdd α]
    (a : WithBot α) : a < 0 ↔ a = ⊥ := by
  induction a <;> simp

