import Mathlib

variable {α : Type u} {β : Type*} [CommMonoid α] [Preorder α]

theorem StrictMono.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β] [LinearOrder β]
    (f : β → α) (hf : StrictMono f) (mul : ∀ x y, f (x * y) = f x * f y) :
    IsOrderedMonoid β := Function.Injective.isOrderedMonoid f mul hf.le_iff_le

