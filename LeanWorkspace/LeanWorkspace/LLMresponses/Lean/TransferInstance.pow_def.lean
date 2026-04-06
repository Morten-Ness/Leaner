import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem pow_def [Pow β M] (n : M) (x : α) :
    letI : Pow α M := ⟨fun a m => e.symm (e a ^ m)⟩
    x ^ n = e.symm (e x ^ n) := rfl
