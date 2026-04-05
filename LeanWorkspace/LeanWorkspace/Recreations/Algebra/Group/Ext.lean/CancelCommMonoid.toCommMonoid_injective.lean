import Mathlib

theorem CancelCommMonoid.toCommMonoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) := by
  rintro @⟨@⟨@⟨⟩⟩⟩ @⟨@⟨@⟨⟩⟩⟩ h
  grind

