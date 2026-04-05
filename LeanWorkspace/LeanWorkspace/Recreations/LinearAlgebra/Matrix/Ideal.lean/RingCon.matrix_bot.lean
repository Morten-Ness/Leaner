import Mathlib

variable {R n : Type*}

variable [NonUnitalNonAssocSemiring R] [Fintype n]

theorem matrix_bot : (⊥ : RingCon R).matrix n = ⊥ := eq_bot_iff.2 fun _ _ h ↦ Matrix.ext h

