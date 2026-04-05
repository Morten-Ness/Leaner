import Mathlib

variable (R : Type u)

theorem tropEquiv_symm_coe_fn : (Tropical.tropEquiv.symm : Tropical R → R) = Tropical.untrop := rfl

