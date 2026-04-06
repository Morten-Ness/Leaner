import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_inl [DecidablePred fun x : G₀ ↦ x = 0] (x : G₀) :
    MonoidWithZeroHom.fst _ H₀ (MonoidWithZeroHom.inl _ _ x) = x := by
  by_cases hx : x = 0
  · simp [MonoidWithZeroHom.fst, MonoidWithZeroHom.inl, hx]
  · simp [MonoidWithZeroHom.fst, MonoidWithZeroHom.inl, hx]
