import Mathlib

section

variable {M α β : Type*} (e : α ≃ β)

theorem div_def [Div β] (x y : α) :
    letI := Equiv.div e
    x / y = e.symm (e x / e y) := rfl

-- Porting note: this should be called `inv`,
-- but we already have an `Equiv.inv` (which perhaps should move to `Perm.inv`?)

end

section

variable {M α β : Type*} (e : α ≃ β)

theorem inv_def [Inv β] (x : α) :
    letI := e.Inv
    x⁻¹ = e.symm (e x)⁻¹ := rfl

end

section

variable {M α β : Type*} (e : α ≃ β)

theorem mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI := Equiv.mul e
    (Equiv.mulEquiv e).symm b = e.symm b := rfl

end

section

variable {M α β : Type*} (e : α ≃ β)

theorem mul_def [Mul β] (x y : α) :
    letI := Equiv.mul e
    x * y = e.symm (e x * e y) := rfl

end

section

variable {M α β : Type*} (e : α ≃ β)

theorem pow_def [Pow β M] (n : M) (x : α) :
    letI := e.pow M
    x ^ n = e.symm (e x ^ n) := rfl

end
