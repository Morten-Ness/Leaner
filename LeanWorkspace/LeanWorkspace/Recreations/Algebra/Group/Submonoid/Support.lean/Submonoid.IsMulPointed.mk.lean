import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem mk (h : ∀ x ∈ M, x⁻¹ ∈ M → x = 1) : M.IsMulPointed := h -- for Aesop

