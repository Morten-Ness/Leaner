import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem iUnion_inv_smul : ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s := (Function.Surjective.iSup_congr _ inv_surjective) fun _ ↦ rfl

