import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

theorem covariant_lt_iff_contravariant_le [LinearOrder N] :
    Covariant M N μ (· < ·) ↔ Contravariant M N μ (· ≤ ·) := ⟨fun h _ _ _ bc ↦ not_lt.mp fun k ↦ bc.not_gt (h _ k),
   fun h _ _ _ bc ↦ not_le.mp fun k ↦ bc.not_ge (h _ k)⟩

