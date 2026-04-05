import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem Function.Injective.mulPosMono [MulPosMono α] {β : Type*} [Zero β] [Mul β] [Preorder β]
    (f : β → α) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) : MulPosMono β where
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    rw [← le, mul, mul]; exact mul_le_mul_of_nonneg_right (le.2 hbc) (by rwa [← zero, le])

