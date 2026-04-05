import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem preimage_smul₀ (ha : a ≠ 0) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t := preimage_smul (Units.mk0 a ha) t

