import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem mk (h : ∀ a : G, a ∈ M ∨ a⁻¹ ∈ M) : M.IsMulSpanning := h -- for Aesop

