import Mathlib

variable {α : Type u} {β : Type*} [CommMonoid α] [Preorder α]

theorem StrictMono.isOrderedCancelMonoid [IsOrderedCancelMonoid α] [CommMonoid β] [LinearOrder β]
    (f : β → α) (hf : StrictMono f) (mul : ∀ x y, f (x * y) = f x * f y) :
    IsOrderedCancelMonoid β where
  __ := hf.isOrderedMonoid f mul
  le_of_mul_le_mul_left a b c h := by simpa [← hf.le_iff_le, mul] using h

-- TODO find a better home for the next two constructions.

