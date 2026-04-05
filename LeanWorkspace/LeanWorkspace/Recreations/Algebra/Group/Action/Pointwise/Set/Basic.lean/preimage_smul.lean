import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem preimage_smul (a : α) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t := ((MulAction.toPerm a).image_symm_eq_preimage _).symm

