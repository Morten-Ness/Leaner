import Mathlib

variable {M : Type*} {S T : Set M}

variable [Semigroup M] {a b : M}

theorem Set.mem_center_iff _root_.Semigroup {z : M} :
    z ∈ Set.center M ↔ ∀ g, g * z = z * g := ⟨fun a g ↦ by rw [IsMulCentral.comm a g],
  fun h ↦ ⟨fun _ ↦ (h _).symm, fun _ _ ↦ (mul_assoc z _ _).symm, fun _ _ ↦ mul_assoc _ _ z⟩ ⟩

