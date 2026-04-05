import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem mem_or_inv_mem (hM : M.IsMulSpanning) (a : G) : a ∈ M ∨ a⁻¹ ∈ M := by aesop

