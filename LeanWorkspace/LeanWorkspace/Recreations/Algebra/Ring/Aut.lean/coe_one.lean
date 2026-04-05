import Mathlib

variable (R : Type*) [Mul R] [Add R]

theorem coe_one : ⇑(1 : R ≃+* R) = id := rfl

