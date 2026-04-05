import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoidWithOne R]

theorem one_eq_mrange : (1 : AddSubmonoid R) = AddMonoidHom.mrange (Nat.castAddMonoidHom R) := rfl

