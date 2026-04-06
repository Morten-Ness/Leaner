import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem inv_product [DecidableEq β] [InvolutiveInv β] (s : Finset α) (t : Finset β) :
    (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹ := by
  ext x
  rcases x with ⟨a, b⟩
  simp [Finset.mem_inv, and_left_comm, and_assoc]
