import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem Function.Injective.mulPosStrictMono [MulPosStrictMono α] {β : Type*} [Zero β] [Mul β]
    [Preorder β] (f : β → α) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)
    (lt : ∀ {x y}, f x < f y ↔ x < y) : MulPosStrictMono β where
  mul_lt_mul_of_pos_right a ha b c hbc := by
    rw [← lt, mul, mul]; exact mul_lt_mul_of_pos_right (lt.2 hbc) (by rwa [← zero, lt])

