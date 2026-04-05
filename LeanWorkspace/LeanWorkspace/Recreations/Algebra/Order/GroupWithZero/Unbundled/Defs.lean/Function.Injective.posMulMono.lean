import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem Function.Injective.posMulMono [PosMulMono α] {β : Type*} [Zero β] [Mul β] [Preorder β]
    (f : β → α) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) : PosMulMono β where
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← le, mul, mul]; exact mul_le_mul_of_nonneg_left (le.2 hbc) (by rwa [← zero, le])

