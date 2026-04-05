import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem mem_normalizer_iff {g : G} : g ∈ Subgroup.normalizer H ↔ ∀ h, h ∈ H ↔ g * h * g⁻¹ ∈ H := Iff.rfl

