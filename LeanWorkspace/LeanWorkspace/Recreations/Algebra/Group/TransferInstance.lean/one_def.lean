import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem one_def [One β] :
    letI := e.one
    1 = e.symm 1 := rfl

