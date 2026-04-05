import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_insert (a : α) (s : Set α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ := by
  rw [insert_eq, Set.union_inv, Set.inv_singleton, insert_eq]

