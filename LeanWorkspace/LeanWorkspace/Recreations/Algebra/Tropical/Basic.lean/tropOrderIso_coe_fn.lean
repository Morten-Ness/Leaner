import Mathlib

variable (R : Type u)

theorem tropOrderIso_coe_fn [Preorder R] : (Tropical.tropOrderIso : R → Tropical R) = Tropical.trop := rfl

