import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

theorem covariantClass_le_of_lt [PartialOrder N] [CovariantClass M N μ (· < ·)] :
    CovariantClass M N μ (· ≤ ·) := ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩

