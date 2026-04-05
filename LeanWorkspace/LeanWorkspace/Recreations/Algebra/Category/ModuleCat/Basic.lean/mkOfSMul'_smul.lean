import Mathlib

variable (R : Type u) [Ring R]

variable {X₁ X₂ : Type v}

variable (M N : ModuleCat.{v} R)

variable {A : AddCommGrpCat} (φ : R →+* End A)

theorem mkOfSMul'_smul (r : R) (x : ModuleCat.mkOfSMul' φ) :
    r • x = (show A ⟶ A from φ r) x := rfl

