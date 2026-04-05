import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) := fun a _ _ ↦ h a

