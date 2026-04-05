import Mathlib

variable {S₁ : Type*} {S₂ : Type*} {S₃ : Type*} [Shelf S₁] [Shelf S₂] [Shelf S₃]

theorem map_act (f : S₁ →◃ S₂) {x y : S₁} : f (x ◃ y) = f x ◃ f y := map_act' f

