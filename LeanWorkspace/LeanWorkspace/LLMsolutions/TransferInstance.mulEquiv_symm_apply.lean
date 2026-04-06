FAIL
import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI : Mul α := ⟨fun x y => e.symm (e x * e y)⟩
    e ((e.symm b) * (e.symm b)) = b * b := by
  simp [Mul.mul]
