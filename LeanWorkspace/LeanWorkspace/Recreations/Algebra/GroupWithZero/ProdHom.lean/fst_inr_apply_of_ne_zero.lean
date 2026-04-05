import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_inr_apply_of_ne_zero [DecidablePred fun x : H₀ ↦ x = 0] {x : H₀} (hx : x ≠ 0) :
    MonoidWithZeroHom.fst _ _ (MonoidWithZeroHom.inr G₀ _ x) = 1 := by
  rw [← MonoidWithZeroHom.comp_apply, MonoidWithZeroHom.fst_comp_inr, one_apply_of_ne_zero hx]

