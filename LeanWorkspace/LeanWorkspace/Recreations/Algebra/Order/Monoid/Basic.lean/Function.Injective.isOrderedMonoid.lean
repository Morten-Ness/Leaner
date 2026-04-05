import Mathlib

variable {α : Type u} {β : Type*} [CommMonoid α] [Preorder α]

theorem Function.Injective.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β]
    [Preorder β] (f : β → α) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) :
    IsOrderedMonoid β where
  mul_le_mul_left a b ab c := le.1 <| by rw [mul, mul]; grw [le.2 ab]

