import Mathlib

theorem CommGroup.toGroup_injective {G : Type*} : Function.Injective (@CommGroup.toGroup G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

