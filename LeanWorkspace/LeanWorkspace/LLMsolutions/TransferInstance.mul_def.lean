import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem mul_def [Mul β] (x y : α) :
    letI : Mul α := ⟨fun a b => e.symm (e a * e b)⟩
    x * y = e.symm (e x * e y) := rfl
