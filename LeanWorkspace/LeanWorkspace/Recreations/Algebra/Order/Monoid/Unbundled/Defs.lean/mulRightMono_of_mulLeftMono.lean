import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem mulRightMono_of_mulLeftMono [CommSemigroup N] [LE N] [MulLeftMono N] :
    MulRightMono N := inferInstance

