import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [MulOneClass α]

theorem subset_mul_right {s : Finset α} (t : Finset α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun a ha =>
  Finset.mem_mul.2 ⟨1, hs, a, ha, one_mul _⟩

