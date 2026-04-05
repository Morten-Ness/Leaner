import Mathlib

variable (R : Type u)

theorem tropEquiv_coe_fn : (Tropical.tropEquiv : R → Tropical R) = Tropical.trop := rfl

