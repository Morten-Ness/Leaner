import Mathlib

variable {A M G α β γ : Type*}

theorem _root_.Equiv.permCongr_eq_mul (e p : Equiv.Perm α) : e.permCongr p = e * p * e⁻¹ := rfl

