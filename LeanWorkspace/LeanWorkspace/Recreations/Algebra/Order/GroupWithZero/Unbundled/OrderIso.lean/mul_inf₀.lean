import Mathlib

variable {G₀ : Type*} [GroupWithZero G₀]

theorem mul_inf₀ [SemilatticeInf G₀] [PosMulReflectLT G₀] {c : G₀} (hc : 0 ≤ c) (a b : G₀) :
    c * (a ⊓ b) = c * a ⊓ c * b := by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulLeft₀ c hc).map_inf a b

