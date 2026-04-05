import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_injective [InvolutiveStar R] : Function.Injective (star : R → R) := Function.Involutive.injective star_involutive

