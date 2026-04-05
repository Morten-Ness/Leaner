import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem pow_def [Pow β M] (n : M) (x : α) :
    letI := e.pow M
    x ^ n = e.symm (e x ^ n) := rfl

