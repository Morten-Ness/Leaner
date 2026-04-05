import Mathlib

variable (R : Type u)

theorem trop_smul {α : Type*} [SMul α R] (x : R) (n : α) : Tropical.trop (n • x) = Tropical.trop x ^ n := rfl

