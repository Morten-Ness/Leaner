import Mathlib

theorem Group.toDivInvMonoid_injective {G : Type*} : Function.Injective (@Group.toDivInvMonoid G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

