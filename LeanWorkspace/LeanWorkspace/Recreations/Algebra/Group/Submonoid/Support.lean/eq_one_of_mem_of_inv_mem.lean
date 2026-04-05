import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem eq_one_of_mem_of_inv_mem (hM : M.IsMulPointed)
    {x : G} (hx₁ : x ∈ M) (hx₂ : x⁻¹ ∈ M) : x = 1 := hM _ hx₁ hx₂

