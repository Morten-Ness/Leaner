import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem mem_smul_set_inv {s : Set α} : a ∈ b • s⁻¹ ↔ b ∈ a • s := by
  simp [Set.mem_smul_set_iff_inv_smul_mem]

