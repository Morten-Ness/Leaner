import Mathlib

variable (R : Type u)

theorem tropOrderIso_symm_coe_fn [Preorder R] : (Tropical.tropOrderIso.symm : Tropical R → R) = Tropical.untrop := rfl

