import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem inv_def [Inv β] (x : α) :
    letI := e.Inv
    x⁻¹ = e.symm (e x)⁻¹ := rfl

