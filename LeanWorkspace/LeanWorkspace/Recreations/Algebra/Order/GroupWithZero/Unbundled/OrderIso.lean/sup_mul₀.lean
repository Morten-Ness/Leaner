import Mathlib

variable {G₀ : Type*} [GroupWithZero G₀]

theorem sup_mul₀ [SemilatticeSup G₀] [MulPosReflectLT G₀] {c : G₀} (hc : 0 ≤ c) (a b : G₀) :
    (a ⊔ b) * c = a * c ⊔ b * c := by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulRight₀ c hc).map_sup a b

