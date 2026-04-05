import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem mulSupport_toSubmonoid : M.mulSupport.toSubmonoid = M ⊓ M⁻¹ := rfl

