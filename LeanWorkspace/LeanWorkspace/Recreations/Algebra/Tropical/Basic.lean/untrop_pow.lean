import Mathlib

variable (R : Type u)

theorem untrop_pow {α : Type*} [SMul α R] (x : Tropical R) (n : α) :
    Tropical.untrop (x ^ n) = n • Tropical.untrop x := rfl

