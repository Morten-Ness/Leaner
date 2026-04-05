import Mathlib

variable {α : Type u} {β : Type*} [CommMonoid α] [Preorder α]

theorem Function.Injective.isOrderedCancelMonoid [IsOrderedCancelMonoid α] [CommMonoid β]
    [Preorder β]
    (f : β → α) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) :
    IsOrderedCancelMonoid β where
  __ := Function.Injective.isOrderedMonoid f mul le
  le_of_mul_le_mul_left a b c bc := le.1 <|
      (mul_le_mul_iff_left (f a)).1 (by rwa [← mul, ← mul, le])

