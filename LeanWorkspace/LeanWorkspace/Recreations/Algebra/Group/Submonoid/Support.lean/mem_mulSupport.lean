import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem mem_mulSupport {x} : x ∈ M.mulSupport ↔ x ∈ M ∧ x⁻¹ ∈ M := .rfl

