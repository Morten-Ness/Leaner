import Mathlib

variable {α β γ : Type*}

variable [Group α]

theorem coe_unitsWithZeroEquiv_eq_units_val (γ : (WithZero α)ˣ) :
    ↑(WithZero.unitsWithZeroEquiv γ) = γ.val := by
  simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]

