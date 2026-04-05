import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) := fun a _ _ ↦ h a

