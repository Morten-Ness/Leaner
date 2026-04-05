import Mathlib

variable {G : Type*}

variable [DivInvMonoid G]

theorem zpow_neg_one (x : G) : x ^ (-1 : ℤ) = x⁻¹ := (zpow_negSucc x 0).trans <| congr_arg Inv.inv (pow_one x)

