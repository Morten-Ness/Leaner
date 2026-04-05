import Mathlib

variable {R : Type*} [Semiring R]

theorem mulRight_apply (u : Rˣ) (x : R) : AddAut.mulRight u x = x * u := rfl

