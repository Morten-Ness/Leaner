FAIL
import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (MonoidWithZeroHom.fst ..).comp (MonoidWithZeroHom.inr G₀ H₀) = 1 := by
  ext x
  by_cases hx : x = 0
  · simp [MonoidWithZeroHom.inr, hx]
  · simp [MonoidWithZeroHom.inr, hx, one_def]
