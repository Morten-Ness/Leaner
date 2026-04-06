import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem out_injective : Function.Injective (Associates.out : _ → α) := by
  intro a b h
  simpa using Associates.out_injective h
