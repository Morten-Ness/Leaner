import Mathlib

variable (R : Type u) [Ring R]

variable {X₁ X₂ : Type v}

variable (M N : ModuleCat.{v} R)

variable {A : AddCommGrpCat} (φ : R →+* End A)

set_option backward.isDefEq.respectTransparency false in
theorem mkOfSMul_smul (r : R) : (mkOfSMul φ).smul r = φ r := rfl

