import Mathlib

variable (R : Type*) [Mul R] [Add R]

theorem mul_apply (f g : R ≃+* R) (x : R) : (f * g) x = f (g x) := rfl

