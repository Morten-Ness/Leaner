import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem preimage_smul_inv (a : α) (t : Set β) : (fun x ↦ a⁻¹ • x) ⁻¹' t = a • t := Set.preimage_smul (toUnits a)⁻¹ t

