import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

theorem contravariant_lt_of_contravariant_le [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) → Contravariant M N μ (· < ·) := And.left ∘ (contravariant_le_iff_contravariant_lt_and_eq M N μ).mp

