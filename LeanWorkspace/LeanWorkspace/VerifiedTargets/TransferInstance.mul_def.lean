import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem mul_def [Mul β] (x y : α) :
    letI := Equiv.mul e
    x * y = e.symm (e x * e y) := rfl

