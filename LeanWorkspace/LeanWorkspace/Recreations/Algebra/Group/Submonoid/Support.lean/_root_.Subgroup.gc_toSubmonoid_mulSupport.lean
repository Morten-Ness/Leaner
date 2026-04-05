import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem _root_.Subgroup.gc_toSubmonoid_mulSupport :
    GaloisConnection (α := Subgroup G) Subgroup.toSubmonoid Submonoid.mulSupport :=
  fun _ _ ↦ ⟨fun _ _ ↦ by aesop, fun h _ hx ↦ (h hx).1⟩

