import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem _root_.isMulPointed_iff_mulSupport_eq_bot : M.IsMulPointed ↔ M.mulSupport = ⊥ where
  mp := by aesop
  mpr h := fun x ↦ by
    apply_fun (x ∈ ·) at h
    aesop

