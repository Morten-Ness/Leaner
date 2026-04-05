import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (MonoidWithZeroHom.fst ..).comp (MonoidWithZeroHom.inr G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.fst, MonoidWithZeroHom.inr]

