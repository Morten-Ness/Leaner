import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem Function.Injective.posMulStrictMono [PosMulStrictMono α] {β : Type*} [Zero β] [Mul β]
    [Preorder β] (f : β → α) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)
    (lt : ∀ {x y}, f x < f y ↔ x < y) : PosMulStrictMono β where
  mul_lt_mul_of_pos_left a ha b c hbc := by
    rw [← lt, mul, mul]; exact mul_lt_mul_of_pos_left (lt.2 hbc) (by rwa [← zero, lt])

