import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

theorem ofBoolAlg_sup (a b : AsBoolAlg α) :
    ofBoolAlg (a ⊔ b) = ofBoolAlg a + ofBoolAlg b + ofBoolAlg a * ofBoolAlg b := rfl

