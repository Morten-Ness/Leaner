import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (MonoidWithZeroHom.fst ..).comp (MonoidWithZeroHom.inl G₀ H₀) = .id _ := by
  ext x
  by_cases hx : x = 0
  · simp [MonoidWithZeroHom.inl, MonoidWithZeroHom.fst, hx]
  · simp [MonoidWithZeroHom.inl, MonoidWithZeroHom.fst, hx]
